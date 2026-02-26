# File Organizer - 高效能大量媒體檔案整理工具 (v1.9.0 企業級最終版)

這是一個專為處理 **TB 級資料量**、**數百萬個破碎檔案** (如 200 萬 - 300 萬個圖片/影片) 所設計的 Python 高性能整理工具。它採用多執行緒與生產者-消費者架構，能精準解析 EXIF 元數據、檔案名稱或 Google Takeout JSON，並將混亂的媒體檔案自動歸類到結構化的目錄中。

## 🌟 核心特色

*   **極致效能架構**：採用「生產者-消費者」(Producer-Consumer) 模式，結合多執行緒 (Multi-threading) 與任務隊列 (Queue)，在高併發 I/O 環境下仍能保持低記憶體消耗與極高處理速度。
*   **三重智慧日期解析**：
    *   **EXIF 解析**：精確提取圖片內的拍攝時間。
    *   **檔名正則解析**：支援多種日期格式 (YYYYMMDD, YYYY-MM-DD 等) 與 Unix Timestamp (10位/13位)。
    *   **Google Takeout 支援**：完美處理 Google 匯出的無 EXIF 檔案，自動關聯 `.json` 檔案並解析 `photoTakenTime`。
*   **Google Takeout 特殊處理**：
    *   **時區自動轉換**：將 Takeout 的 UTC 時間自動轉換為 **台灣時間 (UTC+8)**。
    *   **自動改名功能**：針對 Takeout 或 EXIF 模式下的 `IMG_數字` 檔案，自動更名為 `IMG_日期_時間.EXT` (如 `IMG_20231225_143000.JPG`)。
*   **企業級安全去重 (Deduplication)**：
    *   比對邏輯：檔案大小 (Size) -> 4K 區塊採樣 -> 全檔案 MD5 哈希。
    *   確保目標已存在且內容完全一致時，才執行刪除來源的操作。
*   **原子化與安全操作**：
    *   支援 `dry-run` 模擬模式。
    *   複製模式下使用 `shutil.copy2` 完整保留 `ctime`/`mtime`/`atime` 檔案屬性。
    *   支援 `--touch` 功能，強制校正檔案系統時間為拍攝日期。

## 🛠️ 環境需求

*   **Python 版本**：建議 3.10+
*   **必要套件**：
    ```bash
    pip install loguru Pillow
    ```

## 🚀 快速上手

### 基本語法
```bash
python3 file_organizer.py --target [目標目錄] [來源目錄1] [來源目錄2] ...
```

### 常用情境範例

1.  **安全模擬執行 (Dry-run)**：不改動檔案，僅預覽處理結果。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/raw -n
    ```

2.  **整理 Google Takeout 匯出資料**：自動處理 JSON 關聯、轉換時區並更名。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/Takeout --mode takeout --move
    ```

3.  **高性能多線程搬移 + 刪除重複來源**：使用 16 個執行緒加速。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/backup -w 16 --move --delete
    ```

4.  **校正相簿檔案時間**：將檔案修改時間 (`mtime`) 強制同步為拍攝時間。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/backup --touch
    ```

## 📖 參數說明

| 參數 | 縮寫 | 預設值 | 說明 |
| :--- | :--- | :--- | :--- |
| `sources` | | (必填) | 來源目錄 (支援多個路徑)。 |
| `--target` | `-t` | (必填) | 目標根目錄。 |
| `--mode` | `-m` | `auto` | 解析模式：`exif`, `filename`, `takeout` (可用逗號指定順序)。 |
| `--type` | | `auto` | 處理類型：`img`, `media` (圖片+影片), `auto`。 |
| `--dry-run`| `-n` | `False` | 模擬執行，不變更任何檔案。 |
| `--workers`| `-w` | `4` | 併發處理執行緒數量。 |
| `--copy` | `-c` | `True` | 預設複製檔案。 |
| `--move` | | `False` | 搬移檔案 (安全移動)。 |
| `--delete` | | `False` | 若目標與來源完全一致，則刪除來源 (包含關聯 JSON)。 |
| `--touch` | | `False` | 強制修改檔案 `mtime` 為拍攝日期。 |
| `--queue` | | `100000`| 任務隊列積壓上限，控制記憶體佔用。 |

## 🔍 日期解析邏輯 (`--mode`)

1.  **`exif`**：讀取圖片 EXIF 標記。若檔名為 `IMG_數字` 格式，會自動更名。
2.  **`filename`**：正則過濾檔名。影片檔案強制僅使用此模式。
3.  **`takeout`**：
    *   僅處理檔名以 `IMG_` 開頭且無 EXIF、無檔名日期資訊的檔案。
    *   尋找同名 `.json` 檔案並讀取 `photoTakenTime`。
    *   自動更名為 `IMG_YYYYMMDD_HHMMSS`。
    *   搬移或刪除時，會一併清理對應的 `.json` 檔案。
4.  **`auto`**：預設模式，執行 `exif,filename` (EXIF 優先)。

## 📂 整理後的目錄結構

層級結構：`年 / 月 / 日期 (YYYY.MM.DD) / 檔案`
```text
/目標目錄/
└── 2013/
    └── 12/
        └── 2013.12.21/
            └── IMG_20131221_155922.jpg
```

## 📈 監控與日誌

*   **實時監控**：背景執行緒每 **5 秒** 報告一次 Queue 積壓狀況。
*   **統計回報**：每處理 **1000 筆** 檔案，會回報當前進度、批次耗時與處理速度 (files/sec)。
*   **詳細日誌**：使用 `loguru`，輸出包含執行時間、行數與等級。
    *   `INFO`: 顯示檔案操作細節。
    *   `DEBUG`: 顯示忽略原因 (如無日期資訊)。
    *   `ERROR`: 顯示崩潰或權限問題。

## 📜 版本紀錄 (Version History)

*   **v1.9.0 (2026-02-24)**: 新增 `exif` 模式下 `IMG_數字` 的自動改名功能。
*   **v1.8.2 (2026-02-23)**: 優化進度統計，加入批次耗時回報。
*   **v1.7.0 (2026-02-21)**: 新增 `takeout` 模式與 UTC+8 時區轉換。
*   **v1.0.0 (2026-02-16)**: 初始版本釋出。

---
**Author**: System Admin  
**License**: MIT  
**Compliance**: Strict PEP 8 Compliance
