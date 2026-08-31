# KoreaderAIplus — KOReader AI 阅读助手 / AI Reading Assistant

KOReader 上的 AI 伴读插件（**仅支持 DeepSeek**，需自备 API Key）。轻量模式划词即问即答，精读模式面向大部头名著/文献。

An AI reading companion plugin for KOReader (**DeepSeek only**, bring your own API Key). Lightweight mode answers on word-selection; Intensive Reading mode targets long novels and literature.

> 本仓库为 KOReader AI 阅读助手插件的合并自改版（KOAI 与 AI Reading Assistant 合并，v1.34）。仅供学习交流，请遵守 DeepSeek 及模型服务商的使用条款。
> This repo is a merged, personally-modified build of the KOReader AI reading assistant (KOAI merged with AI Reading Assistant, v1.34). For learning and communication only — comply with DeepSeek's terms of service.

---

## ✨ 功能 / Features

### 轻量模式（默认）/ Lightweight Mode (default)

- 5 个划词菜单：学术概念解析／英语句子翻译／人文历史解读／通用语境赏析／古文典籍解读（可自定义增删改）
  Five word-selection menus: concept explainer / translation / humanities / context appreciation / classical-Chinese — all customizable.
- 词典弹窗左下角「KOAI 词典」 — KOAI dictionary in the dictionary popup.
- 结果窗口可**追问**、可**保存为笔记**、可查看**历史** — follow-up questions, save to notes, browse history.
- 启动只加载最小模块集，待机内存占用低，不自动联网，不费 token — minimal startup footprint, no auto network, no token burn.

### 精读模式（默认关闭）/ Intensive Reading Mode (off by default)

- 划词自动附带**已读上下文**（基于本地采集的实际翻阅内容）+ 防剧透规则 — selected-word answers carry your reading context, spoiler-guarded.
- **人物／典故**划词卡片、人物关系、故事线、时间线 — character/allusion cards, relationships, story arcs, timelines.
- 当前进度复盘、前序阅读状态回溯补档、全书阅读档案（可导出 Markdown）— progress recaps, backfill, whole-book archive (Markdown export).
- 超过 10 小时未读自动提示前情回顾 — auto "recap before you continue" after 10h away.
- 结果富文本分层显示、本地数据管理 — rich-text layered results, local data management.

## 📦 安装 / Installation

1. 设备连接电脑，进入 `koreader/plugins/` 目录
   Connect the device, open `koreader/plugins/`.
2. 把 `koai.koplugin` 整个文件夹复制到 `koreader/plugins/` 下
   Copy the whole `koai.koplugin` folder into `koreader/plugins/`.
3. 用记事本打开 `koai.koplugin/ai_query.lua`，把顶部 `API_KEY = "输入API密钥"` 替换为你的 DeepSeek API Key，保存
   Open `koai.koplugin/ai_query.lua`, replace `API_KEY = "输入API密钥"` with your DeepSeek API Key, save.
4. 重启 KOReader — Restart KOReader.

> API Key 获取：到 <https://platform.deepseek.com> 注册实名认证，创建 API Key 后充值即可（10 元可用很久）。
> Get a key at <https://platform.deepseek.com> (register, verify, create key, top up — ¥10 lasts a long while).

## 🎛 开关怎么用 / Power Mode Toggle

打开任意书籍 → 顶部菜单 → **工具 → KOAI 设置** → 中部【精读模式 (KOAI): 开/关】

In any book: top menu → **Tools → KOAI Settings** → toggle **Intensive Reading (KOAI)**.

- **关（默认）**：轻量模式，省内存省 token；查看类功能（人物卡、全书档案、阅读回顾）照常可用，生成/采集类功能灰色禁选。
  **Off (default)**: lightweight mode; view-only features stay available, generation/collection features are greyed out.
- **开**：读大部头时打开；划词自动带上下文并出现「人物／典故」按钮，翻页自动采集已读内容（仅存本地，生成复盘才调 AI）。
  **On**: for long reads; word-selection carries context, character/allusion buttons appear, page-turns are collected locally (AI only called for recaps).

## 💾 数据存储 / Data Storage (v1.34+)

| 内容 | 路径 |
|---|---|
| 设置（含 API Key） | `koreader/settings/KOAI_settings.json` |
| 查询历史（上限 50 条） | `koreader/settings/KOAI_history.json` |
| 精读档案（按书分文件夹） | `koreader/data/koaireader/books/` |

旧文件名（`aireadingassistant_*`、`koaireader_settings`）会被自动回读迁移，可放心删除。
Legacy filenames are auto-migrated on first run; safe to delete.

## 📜 许可证 / License

GPL-3.0（见 `koai.koplugin/LICENSE`）。
GPL-3.0 (see `koai.koplugin/LICENSE`).

## 🙏 原作者与鸣谢 / Original Authors & Credits

- **KOAI（KOAI-Reader）** 原作者 / Original author: **mufeng0199**
- **AI Reading Assistant** 原作者 / Original author: **chunbo129**
- **合并与改进 / Merge & improvements**: **ChuckLee93**

感谢以上作者的辛勤创作。本仓库为合并自改版，功能与行为差异见 `安装说明.txt` 的更新记录。
Thanks to the original authors above. This repo is a merged, modified build; see `安装说明.txt` changelog for what changed.
