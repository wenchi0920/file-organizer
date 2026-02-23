# File Organizer - 高效能大量媒體檔案整理工具

這是一個專為處理大規模 (TB 級 / 百萬級檔案) 圖片與影片設計的 Python 工具。它能自動解析檔案的拍攝日期（透過 EXIF、檔名或 Google Takeout JSON），並將其整理至結構化的目錄中。

## 🌟 核心功能

*   **極致效能**：採用多執行緒 (Multi-threading) 與生產者-消費者架構，專為 1T-2T 大小、200-300 萬個破碎檔案設計。
*   **多重日期解析**：支援 EXIF 元數據、檔案名稱規則，以及專門處理 Google Takeout 的 JSON 格式。
*   **安全操作**：支援 `dry-run` 模擬模式，複製檔案時完整保留原始時間屬性 (`ctime`/`mtime`/`atime`)。
*   **智慧去重**：自動比對檔案大小與 MD5 哈希值，確保檔案一致後才執行刪除動作。
*   **自動更名**：在 `takeout` 模式下，能自動將混亂的 `IMG_1234.JPG` 重新命名為 `IMG_YYYYMMDD_HHMMSS.JPG`。

## 🛠️ 安裝需求

請確保您的系統已安裝 Python 3.6+，並安裝以下必要套件：

```bash
pip install loguru Pillow
```

## 🚀 快速上手

### 基本語法
```bash
python3 file_organizer.py --target [目標目錄] [來源目錄1] [來源目錄2] ...
```

### 常用範例

1.  **模擬執行 (Dry-run)**：先確認邏輯是否正確，不更動任何檔案。
    ```bash
    python3 file_organizer.py --target /data/photos /data/old_backup -n
    ```

2.  **正式搬移檔案**：將來源檔案搬移至目標目錄（非複製）。
    ```bash
    python3 file_organizer.py --target /data/photos /data/old_backup --move
    ```

3.  **處理 Google Takeout 檔案**：專門處理從 Google 相簿匯出的檔案（包含 JSON 元數據）。
    ```bash
    python3 file_organizer.py --target /data/photos /data/Takeout --mode takeout --move
    ```

4.  **高併發處理**：使用 16 個執行緒加速整理 200 萬個檔案。
    ```bash
    python3 file_organizer.py --target /data/photos /data/backup -w 16
    ```

## 📖 參數詳細說明

| 參數 | 縮寫 | 說明 |
| :--- | :--- | :--- |
| `sources` | (位置) | 一個或多個來源目錄路徑。 |
| `--target` | `-t` | **(必填)** 整理後的檔案存放根目錄。 |
| `--mode` | `-m` | 日期解析模式：`exif`, `filename`, `takeout`, `auto` (預設為 `auto`)。 |
| `--type` | | 處理類型：`img` (僅圖片), `media` (圖片+影片), `auto` (預設)。 |
| `--dry-run`| `-n` | 模擬執行，僅印出 log 不實際操作檔案。 |
| `--workers`| `-w` | 執行緒數量 (預設 4)。建議根據 CPU 核心數與磁碟 I/O 調整。 |
| `--copy` | `-c` | 僅複製檔案（預設行為，保留來源檔案）。 |
| `--move` | | 搬移檔案（完成後移除來源）。 |
| `--delete` | | 當目標已存在且內容完全一致時，自動刪除來源檔案。 |
| `--touch` | | 強制將檔案的系統修改時間 (`mtime`) 改為偵測到的拍攝時間。 |
| `--queue` | | 任務隊列上限 (預設 100,000)。 |

## 🔍 日期解析模式 (`--mode`) 詳細說明

解析模式決定了程式如何判斷「這張照片是什麼時候拍的」：

*   **`exif`**：讀取圖片內的 EXIF 資訊（拍攝日期）。
*   **`filename`**：從檔名抓取日期，支援 `IMG_20231225_...` 或 `2023-12-25...` 等多種格式。
*   **`takeout`**：**專用模式**。當檔案無法透過 EXIF/檔名判斷時，尋找同名的 `.json` 檔案，讀取 `photoTakenTime` 並轉換為台灣時間（UTC+8）。
    *   *註：此模式僅處理 `IMG_` 開頭的檔案，並會自動執行更名。*
*   **`auto` (預設)**：優先使用 `exif`，若失敗則使用 `filename`。

## 📂 整理後的目錄結構

整理後的檔案會依照 `年/月/日期` 進行歸檔：
```text
/目標目錄/
└── 2023/
    └── 12/
        └── 2023.12.25/
            ├── IMG_20231225_103000.jpg
            └── 旅遊照片.png
```

## ⚠️ 注意事項

1.  **重複檔案處理**：如果目標路徑已存在同名檔案，程式會比對 **檔案大小** 與 **MD5 哈希值**。若完全一樣且開啟 `--move` 或 `--delete`，則會清理來源檔案。
2.  **安全複製**：使用預設複製模式時，程式會執行安全複製 (`shutil.copy2`)，這會連同檔案的原始建立時間與修改時間一併複製。
3.  **日誌監控**：程式每 5 秒會印出一次 Queue 積壓數量，每處理 1000 筆資料會輸出詳細的速度統計。
