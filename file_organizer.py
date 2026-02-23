#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
File Organizer - 高效能大量媒體檔案整理工具 (TB級/百萬檔案專用)

程式說明:
    此工具專為處理大規模 (TB級/百萬級) 圖片與影片檔案設計。
    採用多執行緒 (Multi-threading) 與 生產者-消費者 (Producer-Consumer) 架構，
    有效控制記憶體使用量，並提供極致的檔案搬移/複製效能。

    核心邏輯:
    1. 生產者 (Main Thread): 遞迴掃描來源目錄，過濾檔案類型，放入限制大小的 Queue。
    2. 消費者 (Worker Threads): 從 Queue 取出檔案，解析日期，計算目標路徑。
    3. 監控者 (Monitor Thread): 定期回報 Queue 大小與系統處理速度 (每 5 秒)。
    4. 解析日期策略 (Mode):
       - 圖片: 依據使用者參數決定 Exif 與 Filename 的優先順序。
       - 影片: 強制僅使用 Filename 解析 (無視 Exif 設定)。
       - Takeout: 專門處理 Google Takeout 的檔案，無 EXIF 且檔名無效，
                  且檔名必須以 "IMG_" 開頭時，才讀取 JSON 資訊並改名。
    5. 檔案操作策略:
       - 預設 (--copy): 安全複製 (`shutil.copy2` 保留 ctime/mtime/atime 等屬性)。
       - 搬移 (--move): 直接搬移 (`shutil.move`)。若為 Takeout 模式，一併刪除來源 JSON。
       - 刪除重複 (--delete): 目標已存在且完全一致時，刪除來源檔案 (含關聯 JSON)。
       - 修改時間 (--touch): 強制將檔案修改時間 (mtime/atime) 修改為真實拍攝日期。

版本異動紀錄 (Version History):
    v1.8.2 (2026-02-23)
        - 優化進度回報：在每 1000 筆的統計中加入「批次耗時」資訊 (Req 4)。
        - 完善 Takeout 模式：確保在所有刪除/搬移情境下都能正確清理附屬 JSON。
    v1.8.1 (2026-02-21)
        - 優化 `takeout` 模式：強制規定只有 `IMG_` 開頭的檔案才會觸發 JSON 解析與改名 (Req 18)。
    v1.7.0 (2026-02-21)
        - 新增 `takeout` 模式：支援 Google Takeout JSON 元資料解析。
        - 實作 Takeout UTC 時間轉台灣時間 (UTC+8)。
    v1.6.0 (2026-02-20)
        - 新增獨立的 Queue 監控執行緒。
    v1.0.0 (2026-02-16)
        - 初始版本釋出。

Author: System Admin
PEP 8 Compliance: Strict
"""

import argparse
import hashlib
import json
import os
import queue
import re
import shutil
import sys
import threading
import time
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import List, Optional, Tuple, Set

# -----------------------------------------------------------------------------
# 第三方套件檢查
# -----------------------------------------------------------------------------
try:
    from loguru import logger
    from PIL import Image, UnidentifiedImageError
    import PIL.ExifTags
except ImportError as e:
    print(f"CRITICAL ERROR: 缺少必要套件 ({e.name})。請執行: pip install loguru Pillow")
    sys.exit(1)

# -----------------------------------------------------------------------------
# 全域設定與常數 (Constants)
# -----------------------------------------------------------------------------

IMG_EXTENSIONS: Set[str] = {
    '.jpg', '.jpeg', '.png', '.heic', '.webp', '.bmp', '.tiff', '.tif', '.raw', '.dng'
}
VIDEO_EXTENSIONS: Set[str] = {
    '.mp4', '.mov', '.avi', '.mkv', '.m4v', '.mpg', '.mpeg', '.3gp', '.wmv', '.flv', '.mts'
}

# Regex: 標準日期格式 (支援 YYYYMMDD, YYYY-MM-DD, YYYY.MM.DD)
RE_DATE_STD = re.compile(r'.*?(?<!\d)(\d{4})[-._]?(\d{2})[-._]?(\d{2})(?!\d).*?')

# Regex: Unix Timestamp (捕捉 13位毫秒 或 10位秒)
RE_TIMESTAMP = re.compile(r'.*?(?<!\d)((?:1[0-9]\d{8})|(?:1[0-9]\d{11}))(?!\d).*?')

EXIF_TAG_DATETIME_ORIGINAL = 36867
EXIF_TAG_DATETIME = 306

REPORT_INTERVAL = 1000

# 台灣時區 (UTC+8)
TAIWAN_TZ = timezone(timedelta(hours=8))

# -----------------------------------------------------------------------------
# Loguru 日誌設定
# -----------------------------------------------------------------------------
logger.remove()
logger.add(
    sys.stderr,
    format="<green>{time:YYYY-MM-DD HH:mm:ss.SSS}</green> | <level>{level: <8}</level> | "
           "Line:<cyan>{line: <4}</cyan> | <level>{message}</level>",
    level="INFO",
    enqueue=True
)


# -----------------------------------------------------------------------------
# 核心處理類別 (Core Class)
# -----------------------------------------------------------------------------

class FileOrganizer:
    """檔案整理器核心類別，封裝所有的狀態與操作邏輯。"""

    def __init__(self, args: argparse.Namespace):
        self.sources: List[Path] = [Path(s).resolve() for s in args.sources]
        self.target: Path = Path(args.target).resolve()

        # 操作模式邏輯
        if args.copy and args.move:
            self.operation_mode = 'copy'
        elif args.move:
            self.operation_mode = 'move'
        else:
            self.operation_mode = 'copy'

        self.file_type: str = args.type
        self.dry_run: bool = args.dry_run
        self.allow_delete: bool = args.delete
        self.touch_time: bool = args.touch
        self.workers: int = args.workers
        self.queue_size: int = args.queue

        self.mode_str: str = args.mode
        self.modes: List[str] = self._parse_modes(args.mode)

        self.allowed_extensions: Set[str] = set()
        if self.file_type in ['img', 'auto']:
            self.allowed_extensions.update(IMG_EXTENSIONS)
        if self.file_type in ['media', 'auto']:
            self.allowed_extensions.update(VIDEO_EXTENSIONS)

        self.queue: queue.Queue = queue.Queue(maxsize=self.queue_size)
        self.stop_event = threading.Event()

        self.lock = threading.Lock()
        self.stats = {
            'processed': 0,
            'skipped': 0,
            'deleted': 0,
            'errors': 0
        }
        self.start_time = time.time()
        self.last_report_time = time.time()

    def _parse_modes(self, mode_str: str) -> List[str]:
        # 移除空字串並過濾多餘空格
        raw_modes = [m.strip().lower() for m in mode_str.split(',') if m.strip()]

        if 'takeout' in raw_modes:
            if len(raw_modes) > 1:
                logger.error("參數錯誤: --mode takeout 只能獨立執行，不能與其他模式混用。")
                sys.exit(1)
            return ['takeout']

        # 如果同時包含 auto 與其他模式，依據 Req 8，auto 無效 (移除它)
        if 'auto' in raw_modes and len(raw_modes) > 1:
            raw_modes.remove('auto')

        # 預設模式：如果為空或指定為 auto，則執行 exif, filename (exif 優先)
        if not raw_modes or 'auto' in raw_modes:
            return ['exif', 'filename']

        return raw_modes

    def _get_file_hash_partial(self, filepath: Path, block_size: int = 4096) -> Optional[str]:
        hasher = hashlib.md5()
        try:
            with open(filepath, 'rb') as f:
                buf = f.read(block_size)
                if not buf:
                    return None
                hasher.update(buf)
            return hasher.hexdigest()
        except OSError:
            return None

    def _get_file_hash_full(self, filepath: Path) -> Optional[str]:
        hasher = hashlib.md5()
        try:
            with open(filepath, 'rb') as f:
                for chunk in iter(lambda: f.read(65536), b""):
                    hasher.update(chunk)
            return hasher.hexdigest()
        except OSError:
            return None

    def _are_files_identical(self, src: Path, dst: Path) -> bool:
        try:
            if src.stat().st_size != dst.stat().st_size:
                return False
            if self._get_file_hash_partial(src) != self._get_file_hash_partial(dst):
                return False
            if self._get_file_hash_full(src) != self._get_file_hash_full(dst):
                return False
            return True
        except OSError as e:
            logger.error(f"比對過程中發生系統錯誤: {src} vs {dst} - {e}")
            return False

    def _parse_date_from_filename(self, filename: str) -> Optional[datetime]:
        match_std = RE_DATE_STD.search(filename)
        if match_std:
            try:
                y, m, d = map(int, match_std.groups())
                if 1990 <= y <= 2050 and 1 <= m <= 12 and 1 <= d <= 31:
                    return datetime(y, m, d)
            except ValueError:
                pass

        match_ts = RE_TIMESTAMP.search(filename)
        if match_ts:
            ts_str = match_ts.group(1)
            try:
                ts = int(ts_str)
                if len(ts_str) >= 13:
                    ts = ts / 1000.0
                dt = datetime.fromtimestamp(ts)
                if 1990 <= dt.year <= 2050:
                    return dt
            except (ValueError, OSError, OverflowError):
                pass
        return None

    def _parse_date_from_exif(self, filepath: Path) -> Optional[datetime]:
        try:
            with Image.open(filepath) as img:
                exif = img._getexif()
                if not exif:
                    return None
                for tag_id in [EXIF_TAG_DATETIME_ORIGINAL, EXIF_TAG_DATETIME]:
                    if tag_id in exif:
                        date_str = exif[tag_id]
                        try:
                            clean_date_str = str(date_str).strip('\x00')[:19]
                            dt = datetime.strptime(clean_date_str, "%Y:%m:%d %H:%M:%S")
                            if 1990 <= dt.year <= 2050:
                                return dt
                        except (ValueError, TypeError):
                            continue
        except (UnidentifiedImageError, SyntaxError, OSError, Exception):
            pass
        return None

    def _parse_date_from_takeout_json(self, json_path: Path) -> Optional[datetime]:
        try:
            with open(json_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            if 'photoTakenTime' in data and 'timestamp' in data['photoTakenTime']:
                ts = int(data['photoTakenTime']['timestamp'])
                # UTC -> 台灣時間 (UTC+8)
                dt_utc = datetime.fromtimestamp(ts, tz=timezone.utc)
                dt_tw = dt_utc.astimezone(TAIWAN_TZ).replace(tzinfo=None)
                return dt_tw
        except Exception as e:
            logger.debug(f"JSON 解析失敗: {json_path} - {e}")
        return None

    def _determine_date(self, filepath: Path) -> Tuple[Optional[datetime], str, Optional[Path]]:
        """回傳: (日期物件, 來源字串, 使用的JSON路徑)"""
        ext = filepath.suffix.lower()

        # --- 專屬 Takeout 模式邏輯 (Req 18) ---
        if self.modes == ['takeout']:
            # 條件 1: 檔案名稱必須以 IMG_ 開頭
            if not filepath.name.upper().startswith("IMG_"):
                return None, "", None

            # 條件 2: 必須沒有 EXIF 時間
            if ext in IMG_EXTENSIONS and self._parse_date_from_exif(filepath) is not None:
                return None, "", None

            # 條件 3: 必須無法從檔名判斷出時間
            if self._parse_date_from_filename(filepath.name) is not None:
                return None, "", None

            # 條件滿足，尋找 JSON 檔案。可能出現的三種命名格式：
            base_name = filepath.stem  # 例如 "IMG_1225"
            json_candidates = [
                filepath.parent / f"{filepath.name}.json",  # IMG_1225.JPG.json
                filepath.parent / f"{base_name}.json",  # IMG_1225.json
                filepath.parent / f"{filepath.name}.supplemental-metadata.json"
                # IMG_1225.JPG.supplemental-metadata.json
            ]

            for json_path in json_candidates:
                if json_path.exists():
                    dt = self._parse_date_from_takeout_json(json_path)
                    if dt:
                        return dt, "Takeout", json_path

            return None, "", None

        # --- 一般模式邏輯 ---
        # 影片檔強制僅使用 filename
        current_modes = ['filename'] if ext in VIDEO_EXTENSIONS else self.modes

        for mode in current_modes:
            if mode == 'filename':
                date_obj = self._parse_date_from_filename(filepath.name)
                if date_obj:
                    return date_obj, "Filename", None
            elif mode == 'exif' and ext in IMG_EXTENSIONS:
                date_obj = self._parse_date_from_exif(filepath)
                if date_obj:
                    return date_obj, "EXIF", None

        return None, "Unknown", None

    def _touch_file(self, filepath: Path, dt: datetime) -> None:
        """
        強制修改檔案的時間 (Req 12, 18)。
        注意：在 Linux 系統中，ctime 為 Metadata 變更時間，通常無法直接由使用者空間修改，
        此處主要修改 mtime (修改時間) 與 atime (存取時間)，這在大多數相簿軟體中被視為拍攝時間。
        """
        if self.dry_run:
            logger.info(f"[DRY-RUN] Touch 時間更新 -> {filepath} 變更為 {dt}")
            return
        try:
            timestamp = dt.timestamp()
            os.utime(filepath, (timestamp, timestamp))
        except OSError as e:
            logger.error(f"修改檔案時間失敗: {filepath} - {e}")

    def _execute_operation(self, src: Path, dst: Path, dt: datetime, used_json: Optional[Path]) -> bool:
        """執行搬移或複製操作。"""
        if self.dry_run:
            if self.touch_time:
                self._touch_file(src, dt)
            return True

        try:
            dst.parent.mkdir(parents=True, exist_ok=True)

            if self.operation_mode == 'copy':
                shutil.copy2(src, dst)
            else:
                shutil.move(str(src), str(dst))
                # 搬移模式下，一併刪除已使用的 JSON 檔案
                if used_json and used_json.exists():
                    try:
                        os.remove(used_json)
                        logger.info(f"🗑️ 連同 JSON 一併刪除: {used_json.name}")
                    except OSError:
                        pass

            if self.touch_time:
                self._touch_file(dst, dt)

            return True

        except OSError as e:
            logger.error(f"檔案操作失敗: {src} -> {dst} | Error: {e}")
            if dst.exists() and dst.stat().st_size == 0:
                try:
                    os.remove(dst)
                except OSError:
                    pass
            return False

    def _worker_process(self):
        """消費者執行緒。"""
        while not self.stop_event.is_set():
            try:
                file_path = self.queue.get(timeout=1.0)
            except queue.Empty:
                continue

            try:
                self._process_single_file(file_path)
            except Exception as e:
                logger.error(f"未預期的崩潰: {file_path} - {e}")
                with self.lock:
                    self.stats['errors'] += 1
            finally:
                self.queue.task_done()
                self._update_stats()

    def _process_single_file(self, src_path: Path):
        """處理單一檔案的邏輯。"""

        date_obj, source, used_json = self._determine_date(src_path)

        if not date_obj:
            logger.debug(f"略過 (條件不符或無日期): {src_path}")
            with self.lock:
                self.stats['skipped'] += 1
            return

        target_name = src_path.name

        # Takeout 專屬改名邏輯 (Req 18)
        if source == "Takeout":
            ext = src_path.suffix  # 保留原始副檔名與大小寫
            target_name = date_obj.strftime("IMG_%Y%m%d_%H%M%S") + ext

        year_str = date_obj.strftime("%Y")
        month_str = date_obj.strftime("%m")
        date_folder = date_obj.strftime("%Y.%m.%d")

        dest_dir = self.target / year_str / month_str / date_folder
        dest_path = dest_dir / target_name

        # 衝突檢查
        if dest_path.exists():
            if self._are_files_identical(src_path, dest_path):
                if self.operation_mode == 'move' or self.allow_delete:
                    logger.info(f"重複檔案 (刪除來源): {src_path}")
                    if not self.dry_run:
                        try:
                            os.remove(src_path)
                            # 來源檔案被判定為重複且遭刪除時，附屬的 JSON 也應一併清除
                            if used_json and used_json.exists():
                                os.remove(used_json)
                                logger.info(f"🗑️ 連同重複檔案的 JSON 一併刪除: {used_json.name}")
                        except OSError as e:
                            logger.error(f"刪除來源失敗: {e}")
                    with self.lock:
                        self.stats['deleted'] += 1
                else:
                    logger.info(f"重複檔案 (保留): {src_path} == {dest_path}")
                    with self.lock:
                        self.stats['skipped'] += 1

                if self.touch_time and not self.dry_run:
                    self._touch_file(dest_path, date_obj)
            else:
                logger.warning(f"檔名衝突 (內容不同，略過): {src_path} -> {dest_path}")
                with self.lock:
                    self.stats['skipped'] += 1
            return

        op_name = "複製" if self.operation_mode == 'copy' else "搬移"
        prefix = "[DRY-RUN] " if self.dry_run else ""

        logger.info(f"{prefix}{op_name} [{source}]: {src_path} -> {dest_path}")

        success = self._execute_operation(src_path, dest_path, date_obj, used_json)

        with self.lock:
            if success:
                self.stats['processed'] += 1
            else:
                self.stats['errors'] += 1

    def _update_stats(self):
        """定期列印處理進度與速度 (Req 4)。"""
        with self.lock:
            total = (self.stats['processed'] + self.stats['skipped'] +
                     self.stats['deleted'] + self.stats['errors'])

            if total > 0 and total % REPORT_INTERVAL == 0:
                now = time.time()
                duration = now - self.last_report_time
                if duration > 0:
                    rate = REPORT_INTERVAL / duration
                    logger.info(
                        f"⚡ 進度統計 | 總計: {total} | 成功: {self.stats['processed']} | "
                        f"略過: {self.stats['skipped']} | 刪除來源: {self.stats['deleted']} | "
                        f"批次耗時: {duration:.2f}s | 速度: {rate:.1f} file/s"
                    )
                    self.last_report_time = now

    def _monitor_queue_process(self):
        """背景監控執行緒 (Req 17)。"""
        while not self.stop_event.wait(5.0):
            logger.info(f"📊 系統監控 | Queue 目前積壓數量: {self.queue.qsize()} / {self.queue_size}")

    def run(self):
        """主執行流程。"""
        logger.info(f"啟動整理工具 | Workers: {self.workers} | Mode: {self.modes}")
        logger.info(
            f"操作設定 | Action: {self.operation_mode.upper()} | DeleteDup: {self.allow_delete} | Touch: {self.touch_time}")
        logger.info(f"目標路徑: {self.target}")

        monitor_thread = threading.Thread(target=self._monitor_queue_process, daemon=True)
        monitor_thread.start()

        threads = []
        for _ in range(self.workers):
            t = threading.Thread(target=self._worker_process, daemon=True)
            t.start()
            threads.append(t)

        try:
            for src_root in self.sources:
                if not src_root.exists():
                    logger.error(f"來源路徑不存在: {src_root}")
                    continue

                logger.info(f"開始掃描目錄: {src_root}")
                for root, dirs, files in os.walk(src_root):
                    if self.target in Path(root).parents or Path(root) == self.target:
                        continue

                    for name in files:
                        ext = os.path.splitext(name)[1].lower()
                        if ext in self.allowed_extensions:
                            file_path = Path(root) / name
                            self.queue.put(file_path)

            logger.info("檔案掃描完成，等待背景任務處理...")
            self.queue.join()

        except KeyboardInterrupt:
            logger.warning("接收到中斷訊號 (Ctrl+C)，正在停止...")
            self.stop_event.set()
            while not self.queue.empty():
                try:
                    self.queue.get_nowait()
                    self.queue.task_done()
                except queue.Empty:
                    break
        finally:
            self.stop_event.set()
            for t in threads:
                t.join(timeout=3)

            elapsed = time.time() - self.start_time
            logger.info(f"✅ 任務結束 | 總耗時: {elapsed:.2f}s")
            logger.info(f"🏁 統計: {self.stats}")


# -----------------------------------------------------------------------------
# Main Entry Point
# -----------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="照片整理工具 (v1.8.2 企業最終版)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="使用範例:\n  python3 file_organizer.py -t /dest /src1 --workers 8 --move --mode takeout"
    )

    parser.add_argument('sources', nargs='+', help='來源目錄 (可輸入多個)')
    parser.add_argument('--target', '-t', required=True, help='目標根目錄')
    parser.add_argument('--mode', '-m', default='auto', help='日期解析模式 (exif,filename,takeout)')
    parser.add_argument('--type', default='auto', help='處理類型：img, media, auto')
    parser.add_argument('--dry-run', '-n', action='store_true', help='模擬執行')
    parser.add_argument('--workers', '-w', type=int, default=4, help='執行緒數量')
    parser.add_argument('--queue', type=int, default=100000, help='Queue 大小 (預設 100000)')
    parser.add_argument('--copy', '-c', action='store_true', help='僅複製檔案 (預設)')
    parser.add_argument('--move', action='store_true', help='直接搬移檔案')
    parser.add_argument('--delete', action='store_true', help='目標完全一致時，刪除來源')
    parser.add_argument('--touch', action='store_true', help='強制修改檔案時間為拍攝時間')

    args = parser.parse_args()

    if args.type not in ['img', 'media', 'auto']:
        logger.error("參數錯誤: --type 必須是 img, media 或 auto")
        sys.exit(1)

    organizer = FileOrganizer(args)
    organizer.run()


if __name__ == "__main__":
    main()