# File Organizer - 高效能大量媒體檔案整理工具 (v1.9.0)

這是一個專為處理 **TB 級資料量** (200萬 - 300萬個檔案) 設計的 Python 高性能工具。它能自動從 EXIF 元數據、檔案名稱或 Google Takeout JSON 中解析拍攝日期，並將混亂的媒體檔案整理成結構化的目錄。

## 🌟 核心特色

*   **高性能架構**：採用「生產者-消費者」(Producer-Consumer) 模式，利用多執行緒 (Multi-threading) 同步處理 I/O 與運算，大幅提升處理速度。
*   **智慧日期解析**：支援多重模式 (`exif`, `filename`, `takeout`)，並可自定義優先順序。
*   **Google Takeout 完美支援**：
    *   自動關聯 `.json` 元數據。
    *   **時區轉換**：自動將 UTC 時間轉換為台灣時間 (UTC+8)。
    *   **自動更名**：將 `IMG_1234.JPG` 依據拍攝時間更名為 `IMG_20231225_143000.JPG`。
*   **安全去重機制**：透過「檔案大小 + 4K 採樣 + 全檔案 MD5」三重比對，確保檔案完全一致才執行刪除。
*   **原子化操作**：支援 `dry-run` 模擬模式，並在複製時完整保留 `ctime`/`mtime`/`atime` 檔案屬性。

## 🛠️ 安裝需求

預設環境 Python 3.10+。請安裝以下必要套件：

```bash
pip install loguru Pillow
```

## 🚀 快速上手

### 基本語法
```bash
python3 file_organizer.py --target [目標根目錄] [來源目錄1] [來源目錄2] ...
```

### 常用情境範例

1.  **模擬執行 (Dry-run)**：安全檢查邏輯，不實際更動檔案。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/raw -n
    ```

2.  **整理 Google Takeout 匯出檔**：處理 JSON 關聯並自動轉換時區與改名。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/Takeout --mode takeout --move
    ```

3.  **多執行緒加速整理**：分配 16 個執行緒處理數百萬個小檔案。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/backup -w 16 --delete
    ```

4.  **強制校正檔案系統時間**：整理後將檔案的修改時間 (`mtime`) 改為照片拍攝時間。
    ```bash
    python3 file_organizer.py -t /data/sorted /data/backup --touch
    ```

## 📖 參數說明

| 參數 | 縮寫 | 預設值 | 說明 |
| :--- | :--- | :--- | :--- |
| `sources` | | (必填) | 一個或多個來源目錄路徑。 |
| `--target` | `-t` | (必填) | 整理後的檔案存放根目錄。 |
| `--mode` | `-m` | `auto` | 日期解析模式。可用逗號分隔順序，例如 `exif,filename`。 |
| `--type` | | `auto` | 處理類型：`img` (圖片), `media` (圖片+影片), `auto` (兩者皆處理)。 |
| `--dry-run`| `-n` | `False` | 模擬執行，僅顯示日誌，不改動檔案。 |
| `--workers`| `-w` | `4` | 併發處理的執行緒數量。 |
| `--copy` | `-c` | `True` | **複製模式**：保留來源檔案 (預設行為)。 |
| `--move` | | `False` | **搬移模式**：檔案移動至目標，完成後移除來源。 |
| `--delete` | | `False` | 若目標已存在且內容一致 (MD5 相同)，則移除來源。 |
| `--touch` | | `False` | 強制將檔案 `mtime` 修改為偵測到的拍攝時間。 |
| `--queue` | | `100000`| 任務隊列緩存上限，防止記憶體溢出。 |

## 🔍 解析模式 (`--mode`) 詳細邏輯

*   **`exif`**：優先讀取圖片內的 EXIF DatetimeOriginal 資訊。
*   **`filename`**：透過正則表達式從檔名解析日期 (如 `IMG_20231225...` 或 `2023-12-25...`)。
*   **`takeout`**：
    *   **限制條件**：僅處理檔名為 `IMG_` 開頭的檔案。
    *   **機制**：尋找對應的 `.json` 檔案，讀取 `photoTakenTime`。
    *   **轉換**：自動將 UTC 轉為台灣時區。
    *   **清理**：若使用 `--move` 或 `--delete`，會連同對應的 JSON 檔案一併清理。
*   **`auto`**：等同於 `exif,filename` (EXIF 優先)。

## 📂 目錄結構範例

整理後的檔案將嚴格遵循以下層級：`年/月/日期 (YYYY.MM.DD)`
```text
/目標目錄/
└── 2023/
    └── 12/
        └── 2023.12.25/
            ├── IMG_20231225_103000.jpg (自動更名後)
            └── 20231225_Family.png
```

## ⚠️ 進階說明與安全性

1.  **重複檔案判定**：當目標目錄已存在同名檔案時，程式會執行 MD5 校驗。若內容完全一致且開啟 `--move` 或 `--delete`，來源檔案將被安全移除；若內容不同，則會保留來源並跳過，以防誤刪。
2.  **效能監控**：
    *   每 **5 秒** 更新一次 Queue 積壓狀態，確保生產者沒有卡死。
    *   每處理 **1000 筆** 檔案輸出一次處理速度 (files/sec) 與批次耗時。
3.  **錯誤處理**：對於損壞的圖片 (PIL 無法讀取) 或無效的 JSON，程式會記錄 `DEBUG` 日誌並優雅跳過，不會中斷整體流程。

---
**提示**：針對百萬級檔案，建議將 `--workers` 設定為 CPU 核心數的 1.5 倍，並搭配高品質 SSD 以獲得最佳效能。
