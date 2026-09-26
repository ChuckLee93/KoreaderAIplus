-- KOAI name_replace.lua（v1.36 重构）
-- 人物别名（人名替换）：解决"人名太长难记"的问题。
-- 目标效果：选中书中"光绪"，输入昵称"小光"，一键全书替换，仅本地可见。
--
-- v1.35 教训（上机实证，2026-09-25）：
--   ①"另存缓存书 + switchDocument 切换"模式有硬伤：缓存 epub 进了最近阅读/主页轮播
--     （同封面重复两本），且关书时 ReaderUI 用内存 doc_settings 全量回写 sidecar，
--     把插件写到磁盘的 koai_name_rules 抹掉（与 settings.reader.lua 回写陷阱同源）。
--   ②替换管道本身已验证可用（光绪→小光 在 5/21 章节文件中生效）。
--
-- v1.36 新方案（参照社区 htmlreplacer.koplugin 的 Apply-to-Original 模式）：
--   替换结果直接写回原书文件本身：
--   首次应用前自动把原书备份到 <DataStorage>/koai_name_cache/originals/（只备份一次），
--   生成替换版到临时文件 → reloadDocument 的 after_close_callback 窗口期（文档已关、
--   尚未重开）原子换入原路径 → 重开后即为替换版。
--   同一本书、同一进度、同一封面，不产生新书；"还原本书"随时从备份恢复。
--   规则持久化修复：当前打开的书直接写 ui.doc_settings（内存+flush），
--   不再写第二个 DocSettings 句柄，杜绝被会话回写覆盖。
--   非 EPUB 无法替换正文，但规则仍注入 KOAI AI Prompt（回答统一用昵称）。
--
-- v1.37 新增：
--   ①AI 人名归组（"合并重复人物名"，仅精读模式）：把书中同一人的各种叫法
--     （全名/简称/昵称/称号）归组，一键建立批量替换规则——组内任一叫法已有
--     昵称则自动对齐现有昵称，没有昵称则当场填写（第二步），留空用最简叫法；
--     AI 只出建议（宁漏勿错+判断理由），全部采纳/逐组确认由用户把关；
--   ②规则增加 pending（待生效）标记："替换生效（重载本书）"菜单仅在有
--     待生效规则时可用；应用成功后自动清零；
--   ③"撤销上次合并"：合并前自动存规则快照，一键恢复到合并前状态；
--   ④卡片显示映射：人物与典故页中，规则原文名显示为当前昵称——
--     仅显示层替换，卡片存储不动，与书内替换互不干扰（不打架）。
--
-- v1.38 简化（用户反馈）：
--   ①删除"撤销上次合并"全局快照机制（与"还原本书"概念重叠）；
--   ②别名列表改为按人物（昵称）分组，新增"撤销此人物的合并（删除该人物
--     全部别名）"——规则层面的纠错按人物进行；书文件层面的回退只靠
--     "还原本书"，两级职责清晰不重叠。
--
-- v2.0.9 简化（用户反馈）：
--   ①删除"替换生效（重载本书，仅 EPUB）"独立菜单——改动后的生效改为
--     统一引导：每次保存/启停/删除规则后弹窗询问"是否立即应用到本书"，
--     与添加别名、AI 归组完成后的既有确认模式一致，不再需要单独菜单；
--   ②别名列表用词重写（用户反馈看不懂）：
--     "停用此人物全部别名"→"暂停替换此人物（规则保留，可恢复）"
--     "启用此人物全部别名"→"恢复替换此人物"
--     "撤销此人物的合并（删除全部别名）"→"删除此人物全部别名"。

local lfs = require("libs/libkoreader-lfs")
local logger = require("logger")
local md5 = require("ffi/sha2").md5
local Archiver = require("ffi/archiver")
local DataStorage = require("datastorage")
local DocSettings = require("docsettings")
local NetworkMgr = require("ui/network/manager")
local UIManager = require("ui/uimanager")
local InfoMessage = require("ui/widget/infomessage")
local ConfirmBox = require("ui/widget/confirmbox")
local ButtonDialog = require("ui/widget/buttondialog")
local MultiInputDialog = require("ui/widget/multiinputdialog")
local json = require("json")
local _ = require("gettext")

local NameReplace = {}

local RULES_KEY = "koai_name_rules"
-- v2.7.5：替换生效签名——applyAndReload 成功后记录本次写入书文件的启用规则集，
-- 供全文提及扫描判断"该人物的昵称已写进书文件"，从而免查全部老叫法
local APPLIED_KEY = "koai_name_rules_applied"
local cache_dir = DataStorage:getDataDir() .. "/koai_name_cache"
local backup_dir = cache_dir .. "/originals"

-- ============ 基础工具 ============

local function trim(s)
  if type(s) ~= "string" then return "" end
  return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function escapePattern(s)
  return (s:gsub("[%%%(%)%.%+%-%*%?%[%]%^%$]", "%%%0"))
end

local function escapeReplacement(s)
  return (s:gsub("%%", "%%%%"))
end

local function isEpub(path)
  -- 大小写不敏感：真机上存在 ".EPUB"/".Epub" 扩展名（如卡拉马佐夫兄弟.EPUB），
  -- 之前只匹配小写导致 applyAndReload 误判"非 EPUB"、替换静默不生效
  if type(path) ~= "string" then return false end
  local lower = path:lower()
  return lower:match("%.epub$") ~= nil or lower:match("%.epub3$") ~= nil
end

local function ensureDir(path)
  if lfs.attributes(path, "mode") ~= "directory" then
    lfs.mkdir(path)
  end
end

-- 分块二进制复制（4.5MB 级文件安全）
local function copyFile(src, dst)
  local fin = io.open(src, "rb")
  if not fin then return false end
  local fout = io.open(dst, "wb")
  if not fout then fin:close() return false end
  while true do
    local chunk = fin:read(65536)
    if not chunk then break end
    fout:write(chunk)
  end
  fin:close()
  fout:close()
  return true
end

-- 原子换入：优先 rename（同卷瞬时完成），失败退回复制
local function swapFile(src, dst)
  os.remove(dst)
  local ok = os.rename(src, dst)
  if ok then return true end
  if copyFile(src, dst) then
    os.remove(src)
    return true
  end
  return false
end

-- 读缓存书时代的标记文件（兼容识别"正在阅读替换缓存版"）
local function readOriginalMarker(path)
  local f = io.open(path .. ".original_path", "r")
  if not f then return nil end
  local orig = f:read("*l")
  f:close()
  if orig and orig ~= "" then return orig end
  return nil
end

-- 返回 原书路径, 是否正在阅读替换缓存版（v1.35 遗留形态）
local function getOriginalFile(ui)
  local file = ui and ui.document and ui.document.file
  if not file then return nil, false end
  local orig = readOriginalMarker(file)
  if orig then return orig, true end
  return file, false
end

-- ============ 规则存取（关键修复：打开中的书写 ui.doc_settings） ============
-- 规则结构：{ original = 原文名, nick = 昵称, enabled = true/false,
--             pending = true/false（待生效：改过还没应用到书文件）, created = os.time() }

local function isCurrentDocument(ui, original_file)
  return ui and ui.document and ui.document.file == original_file
end

local function loadRules(ui, original_file, key)
  key = key or RULES_KEY
  if not original_file then return {} end
  -- 当前打开的书：直接读会话内存 doc_settings（KOReader 关书时会一并持久化，
  -- 且不会被会话自己的 flush 覆盖 —— v1.35 的规则丢失根因）
  if isCurrentDocument(ui, original_file) and ui.doc_settings then
    local rules = ui.doc_settings:readSetting(key)
    if type(rules) == "table" then return rules end
    return {}
  end
  -- 书未打开：直接读写磁盘 sidecar 安全（没有会话会覆盖它）
  local ok, settings = pcall(function() return DocSettings:open(original_file) end)
  if not ok or not settings then return {} end
  local rules = settings:readSetting(key)
  if type(rules) ~= "table" then return {} end
  return rules
end

local function saveRules(ui, original_file, rules, key)
  key = key or RULES_KEY
  if not original_file then return end
  local n = type(rules) == "table" and #rules or -1
  logger.info("KOAI NameReplace: saveRules key=", key, " n=", n,
    " curDoc=", tostring(isCurrentDocument(ui, original_file)),
    " docFile=", tostring(ui and ui.document and ui.document.file),
    " origFile=", tostring(original_file))
  if isCurrentDocument(ui, original_file) and ui.doc_settings then
    ui.doc_settings:saveSetting(key, rules)
    local fok, ferr = pcall(function() ui.doc_settings:flush() end)
    logger.info("KOAI NameReplace: flush(curDoc) ok=", tostring(fok), ferr and tostring(ferr) or "")
    return
  end
  local ok, settings = pcall(function() return DocSettings:open(original_file) end)
  if not ok or not settings then
    logger.warn("KOAI NameReplace: saveRules DocSettings open failed")
    return
  end
  settings:saveSetting(key, rules)
  local fok, ferr = pcall(function() settings:flush() end)
  logger.info("KOAI NameReplace: flush(disk) ok=", tostring(fok), ferr and tostring(ferr) or "")
end

-- ============ 模式判断 ============
-- v2.0.9：hasPendingRules 已随"替换生效"菜单删除（改动后由统一引导询问应用）

local function isPowerModeLocal()
  local ok, config = pcall(require, "configuration")
  return ok and type(config) == "table" and config.power_mode == true
end

-- ============ 原书备份与还原 ============

local function getBackupPath(original_file)
  ensureDir(cache_dir)
  ensureDir(backup_dir)
  local base = original_file:match("([^/]+)$") or "book.epub"
  return backup_dir .. "/" .. md5(original_file):sub(1, 8) .. "_" .. base
end

local function ensureBackup(original_file)
  local bp = getBackupPath(original_file)
  if lfs.attributes(bp) then
    logger.info("KOAI NameReplace: backup exists", bp)
    return bp
  end
  if copyFile(original_file, bp) then
    logger.info("KOAI NameReplace: backup created", bp)
    return bp
  end
  return nil
end

local function hasBackup(original_file)
  return lfs.attributes(getBackupPath(original_file)) ~= nil
end

-- ============ EPUB 处理（解包 → 替换 → 重打包到临时文件） ============

local function getTempPath(original_file)
  ensureDir(cache_dir)
  local hash = md5(original_file)
  return cache_dir .. "/" .. hash:sub(1, 16) .. ".replaced.epub", cache_dir .. "/" .. hash:sub(1, 16)
end

-- 清理 v1.35 缓存书遗留（避免主页重复封面）：整段只在检测到时触发
local function cleanupLegacyCache(prefix)
  os.remove(prefix .. ".epub")
  os.remove(prefix .. ".epub.original_path")
  if lfs.attributes(prefix .. ".sdr", "mode") == "directory" then
    os.execute(string.format("rm -rf %q", prefix .. ".sdr"))
  end
end

local function extractEpub(epub_path)
  local temp_base = os.tmpname()
  if not temp_base then
    logger.warn("KOAI NameReplace: os.tmpname() failed")
    return nil
  end
  os.remove(temp_base)
  local temp_dir = temp_base .. "_koai_name"
  if not lfs.mkdir(temp_dir) then
    logger.warn("KOAI NameReplace: mkdir failed:", temp_dir)
    return nil
  end
  local cmd = string.format("unzip -q %q -d %q", epub_path, temp_dir)
  local result = os.execute(cmd)
  if result == 0 or result == true then
    return temp_dir
  end
  logger.warn("KOAI NameReplace: unzip failed, result:", tostring(result))
  os.execute(string.format("rm -rf %q", temp_dir))
  return nil
end

local function processHtmlFile(path, rules)
  local f = io.open(path, "r")
  if not f then return false end
  local content = f:read("*all")
  f:close()

  local new_content = content
  local modified = false
  -- 按原名长度降序替换：长名永远先于其包含的短名（如先换
  -- "德米特里·费奥多罗维奇·卡拉马佐夫"再换"德米特里"），
  -- 避免短名先替换导致长名变成"米佳·费奥多罗维奇·卡拉马佐夫"式残缺结果
  local sorted_rules = {}
  for _, rule in ipairs(rules) do
    sorted_rules[#sorted_rules + 1] = rule
  end
  table.sort(sorted_rules, function(a, b) return #a.original > #b.original end)
  for _, rule in ipairs(sorted_rules) do
    local ok, res = pcall(function()
      return new_content:gsub(escapePattern(rule.original), escapeReplacement(rule.nick))
    end)
    if ok and res ~= new_content then
      new_content = res
      modified = true
    end
  end

  if modified then
    f = io.open(path, "w")
    if f then
      f:write(new_content)
      f:close()
      return true
    end
    logger.warn("KOAI NameReplace: cannot write", path)
  end
  return false
end

local function applyRules(temp_dir, rules)
  local count = 0
  local function walk(dir)
    for entry in lfs.dir(dir) do
      if entry ~= "." and entry ~= ".." then
        local path = dir .. "/" .. entry
        local attr = lfs.attributes(path)
        if attr then
          if attr.mode == "directory" then
            walk(path)
          elseif attr.mode == "file"
              and (path:match("%.x?html$") or path:match("%.xhtml$")) then
            if processHtmlFile(path, rules) then count = count + 1 end
          end
        end
      end
    end
  end
  walk(temp_dir)
  logger.info("KOAI NameReplace: replaced in", count, "html files")
  return count
end

local function repackageEpub(temp_dir, output_path)
  local cache_dir_path = output_path:match("(.*/)")
  if cache_dir_path then ensureDir(cache_dir_path) end
  if lfs.attributes(output_path) then
    os.remove(output_path)
  end

  local writer = Archiver.Writer:new()
  if not writer:open(output_path, "zip") then
    logger.warn("KOAI NameReplace: cannot open archive for writing:", tostring(writer.err))
    return false
  end

  -- EPUB 规范：mimetype 必须是第一个条目且不压缩
  writer:setZipCompression("store")
  local mimetype_content = nil
  local f = io.open(temp_dir .. "/mimetype", "r")
  if f then
    mimetype_content = f:read("*all")
    f:close()
  else
    mimetype_content = "application/epub+zip"
  end
  if not writer:addFileFromMemory("mimetype", mimetype_content) then
    logger.warn("KOAI NameReplace: cannot add mimetype:", tostring(writer.err))
    writer:close()
    return false
  end

  writer:setZipCompression("deflate")
  for entry in lfs.dir(temp_dir) do
    if entry ~= "." and entry ~= ".." and entry ~= "mimetype" then
      local path = temp_dir .. "/" .. entry
      writer:addPath(entry, path, true)
      if writer.err then
        logger.warn("KOAI NameReplace: cannot add", entry, ":", tostring(writer.err))
        writer:close()
        return false
      end
    end
  end
  writer:close()
  logger.info("KOAI NameReplace: repackaged epub ->", output_path)
  return true
end

local function cleanupTempDir(temp_dir)
  if temp_dir and lfs.attributes(temp_dir, "mode") == "directory" then
    os.execute(string.format("rm -rf %q", temp_dir))
  end
end

-- 生成替换版到临时文件（不动原书）
local function processEpub(original_file, rules)
  local temp_path, legacy_prefix = getTempPath(original_file)
  cleanupLegacyCache(legacy_prefix) -- v1.35 缓存书遗留，顺手清掉
  local temp_dir = extractEpub(original_file)
  if not temp_dir then
    return nil, "解压 EPUB 失败（设备上可能缺少 unzip 命令，或文件无法读取）"
  end
  applyRules(temp_dir, rules)
  local ok = repackageEpub(temp_dir, temp_path)
  cleanupTempDir(temp_dir)
  if not ok then return nil, "重打包 EPUB 失败" end
  return temp_path
end

-- ============ 对外：状态查询 ============

function NameReplace.isViewingCache(ui)
  local _, viewing_cache = getOriginalFile(ui)
  return viewing_cache
end

function NameReplace.canReplaceText(ui)
  local original_file = getOriginalFile(ui)
  return isEpub(original_file)
end

function NameReplace.canRestore(ui)
  if not (ui and ui.document) then return false end
  local original_file = getOriginalFile(ui)
  return original_file ~= nil and hasBackup(original_file)
end

-- ============ 对外：添加规则对话框（划词/菜单共用） ============

function NameReplace.showAddRuleDialog(ui, default_original)
  if not (ui and ui.document) then return end
  local original_file = getOriginalFile(ui)
  if not original_file then return end

  default_original = trim(default_original or "")
  local dialog
  dialog = MultiInputDialog:new {
    title = "添加人物别名（全书替换人名）",
    fields = {
      {
        text = default_original,
        hint = _("原文名（书中要被替换的名字）"),
      },
      {
        text = "",
        hint = _("替换为（好记的昵称）"),
      },
    },
    buttons = {
      {
        {
          text = _("取消"),
          callback = function()
            UIManager:close(dialog)
          end,
        },
        {
          text = _("保存"),
          is_enter_default = true,
          callback = function()
            local fields = dialog:getFields()
            local original = trim(fields[1] or "")
            local nick = trim(fields[2] or "")
            UIManager:close(dialog)
            if original == "" or nick == "" then
              UIManager:show(InfoMessage:new {
                text = "原文名和昵称都不能为空。",
                timeout = 3,
              })
              return
            end
            local rules = loadRules(ui, original_file)
            local updated = false
            for _, r in ipairs(rules) do
              if r.original == original then
                r.nick = nick
                r.enabled = true
                r.pending = true -- v1.37：待生效
                updated = true
              end
            end
            if not updated then
              table.insert(rules, {
                original = original,
                nick = nick,
                enabled = true,
                pending = true, -- v1.37：待生效
                created = os.time(),
              })
            end
            saveRules(ui, original_file, rules)

            if isEpub(original_file) then
              UIManager:show(ConfirmBox:new {
                text = "别名已保存：\n" .. original .. " → " .. nick
                    .. "\n\n是否立即应用到本书并重新加载？\n"
                    .. "（替换会直接写进书文件；首次应用前自动备份原书，可随时一键还原）",
                ok_text = "立即应用",
                cancel_text = "稍后",
                ok_callback = function()
                  NameReplace.applyAndReload(ui)
                end,
              })
            else
              UIManager:show(InfoMessage:new {
                text = "别名已保存：\n" .. original .. " → " .. nick
                    .. "\n\n当前书不是 EPUB，无法替换正文显示，但 KOAI 的 AI 回答会自动使用昵称。",
                timeout = 6,
              })
            end
          end,
        },
      },
    },
  }
  UIManager:show(dialog)
  dialog:onShowKeyboard()
end

-- ============ 对外：应用替换（写回原书 + 重载） ============

function NameReplace.applyAndReload(ui)
  if not (ui and ui.document) then return end
  local original_file = getOriginalFile(ui)
  if not isEpub(original_file) then
    UIManager:show(InfoMessage:new {
      text = "正文替换目前仅支持 EPUB 格式。\n（其他格式的别名仍会在 KOAI 的 AI 回答中生效）",
      timeout = 5,
    })
    return
  end

  local rules = loadRules(ui, original_file)
  local enabled = {}
  for _, r in ipairs(rules) do
    if r.enabled and r.original ~= "" and r.nick ~= "" then
      table.insert(enabled, r)
    end
  end
  -- v2.7.5：重建式应用。0 条启用规则时：已有原书备份 → 纯原文重建
  -- （删除/停用全部规则的语义闭环：应用即恢复原文）；从未应用过（无备份）
  -- 则书文件本就是原文，无事可做。
  if #enabled == 0 and not hasBackup(original_file) then
    UIManager:show(InfoMessage:new { text = "没有已启用的别名规则。", timeout = 4 })
    return
  end

  local backup_path = ensureBackup(original_file)
  if not backup_path then
    UIManager:show(InfoMessage:new {
      text = "原书备份失败，已取消替换（为保安全不改动书文件）。",
      timeout = 6,
    })
    return
  end

  UIManager:show(InfoMessage:new {
    text = (#enabled == 0
        and "正在从原书备份重建（恢复原文）…"
        or "正在生成替换版（共 " .. #enabled .. " 条别名）…")
        .. "\n大书可能需要几十秒，请稍候。",
    timeout = 5,
  })
  UIManager:scheduleIn(0.2, function()
    -- v2.7.5：改为"从原书备份重建"——规则是目标状态的声明，应用 = 备份原文
    -- + 当前全部启用规则。删除/停用某人的规则后再应用，该人名自动恢复原文，
    -- 其他人物的替换不受影响（旧增量式只会在已替换文件上叠加，删规则无从回退）。
    local temp_path, err = processEpub(backup_path, enabled)
    if not temp_path then
      UIManager:show(InfoMessage:new {
        text = "生成替换版失败：\n" .. tostring(err),
        timeout = 8,
      })
      return
    end
    -- v1.37：替换版生成成功，清零待生效标记。
    -- v2.7.5 关键修复（真机实证：卡老三规则两次删除均被复活）：重建耗时数十秒，
    -- 期间用户可能又改了规则——落盘前必须重读最新规则，绝不能用应用开始时
    -- 捕获的旧数组回写（那会把重建期间删除的规则原样复活）。
    local rules_now = loadRules(ui, original_file)
    -- pending 只清"本次确实已写进书文件"的规则（enabled 集合）；重建期间
    -- 新增/改动的规则保持 pending，等下一次应用生效。
    local applied_keys = {}
    for _, r in ipairs(enabled) do
      applied_keys[tostring(r.original or "") .. "\1" .. tostring(r.nick or "")] = true
    end
    for _, r in ipairs(rules_now) do
      if applied_keys[tostring(r.original or "") .. "\1" .. tostring(r.nick or "")] then
        r.pending = nil
      end
    end
    saveRules(ui, original_file, rules_now)
    -- v2.7.5：记录本次已写入书文件的启用规则签名（original\1nick 用 \3 连接）。
    -- swapFile 在 reloadDocument 回调里异步执行，签名先记；万一换入失败（极罕见），
    -- 扫描侧有"昵称 0 命中回退全量检索"兜底，不会漏。
    local sig_items = {}
    for _, r in ipairs(enabled) do
      sig_items[#sig_items + 1] = tostring(r.original or "") .. "\1" .. tostring(r.nick or "")
    end
    saveRules(ui, original_file, table.concat(sig_items, "\3"), APPLIED_KEY)
    -- 在 reloadDocument 的 after_close 窗口期（文档已关、尚未重开）原子换入原路径
    if ui.reloadDocument then
      ui:reloadDocument(function()
        if not swapFile(temp_path, original_file) then
          logger.warn("KOAI NameReplace: swap file failed", temp_path, "->", original_file)
        else
          logger.info("KOAI NameReplace: replaced book file", original_file)
        end
      end)
    else
      -- 极旧 KOReader：直接换入后提示手动重开
      if swapFile(temp_path, original_file) then
        UIManager:show(InfoMessage:new {
          text = "替换已写回书文件，请关闭并重新打开本书生效。",
          timeout = 8,
        })
      end
    end
  end)
end

-- ============ 对外：还原本书 ============

function NameReplace.revertToOriginal(ui)
  if not (ui and ui.document) then return end
  local original_file, viewing_cache = getOriginalFile(ui)

  -- v1.35 遗留：正在阅读缓存书 → 直接切回原书
  if viewing_cache and original_file and ui.switchDocument then
    ui:switchDocument(original_file, true)
    return
  end

  if not original_file or not hasBackup(original_file) then
    UIManager:show(InfoMessage:new { text = "没有找到本书的替换前备份。", timeout = 4 })
    return
  end

  UIManager:show(ConfirmBox:new {
    text = "把本书还原为替换前的版本？\n（替换后的内容将丢失，别名规则保留）",
    ok_text = "还原",
    ok_callback = function()
      -- v2.7.5：还原后书文件已不是替换版，清除生效签名（扫描退回全量叫法检索）
      saveRules(ui, original_file, "", APPLIED_KEY)
      local backup_path = getBackupPath(original_file)
      ensureDir(cache_dir)
      local tmp = cache_dir .. "/restore_" .. md5(original_file):sub(1, 8) .. ".epub"
      if not copyFile(backup_path, tmp) then
        UIManager:show(InfoMessage:new { text = "读取备份失败。", timeout = 5 })
        return
      end
      if ui.reloadDocument then
        ui:reloadDocument(function()
          if not swapFile(tmp, original_file) then
            logger.warn("KOAI NameReplace: restore swap failed", tmp, "->", original_file)
          else
            logger.info("KOAI NameReplace: book restored from backup", backup_path)
          end
        end)
      else
        if swapFile(tmp, original_file) then
          UIManager:show(InfoMessage:new {
            text = "已还原，请关闭并重新打开本书生效。",
            timeout = 6,
          })
        end
      end
    end,
  })
end

-- ============ 对外：AI Prompt 注入（所有格式可用） ============

function NameReplace.buildAliasPromptBlock(ui)
  if not (ui and ui.document) then return nil end
  local original_file = getOriginalFile(ui)
  if not original_file then return nil end
  local rules = loadRules(ui, original_file)
  local lines = {}
  for _, r in ipairs(rules) do
    if r.enabled and r.original ~= "" and r.nick ~= "" then
      table.insert(lines, r.original .. " = " .. r.nick)
    end
  end
  if #lines == 0 then return nil end
  return "【人物别名对照】用户已把本书的人名替换为好记的昵称（原名 = 昵称），"
      .. "你的回答请统一使用昵称称呼这些人物：\n" .. table.concat(lines, "\n")
end

-- ============ v1.37：AI 人名归组（合并重复人物名，仅精读模式） ============

-- 从 AI 返回文本中提取 JSON 数组并清洗
local function parseGroupsFromAI(text)
  if type(text) ~= "string" then return nil end
  local i = text:find("[", 1, true)
  if not i then return nil end
  local j
  for k = #text, i, -1 do
    if text:sub(k, k) == "]" then j = k break end
  end
  if not j or j <= i then return nil end
  local ok, data = pcall(json.decode, text:sub(i, j))
  if not ok or type(data) ~= "table" then return nil end
  local groups = {}
  for _, g in ipairs(data) do
    if type(g) == "table" and type(g.names) == "table" and #g.names >= 2 then
      local names = {}
      for _, n in ipairs(g.names) do
        n = trim(tostring(n or ""))
        if n ~= "" then names[#names + 1] = n end
      end
      if #names >= 2 then
        groups[#groups + 1] = {
          names = names,
          canonical = trim(tostring(g.canonical or "")),
          reason = trim(tostring(g.reason or "")),
        }
      end
    end
    if #groups >= 8 then break end
  end
  return groups
end

-- ============ v2.0.4：本地全书人名候选扫描（零 token） ============
-- 教训（卡拉马佐夫实测）：AI 只凭书名/作者归组，写出的"阿列克谢"与荣如德译本的
-- "阿列克塞"对不上，还出现"格鲁申卡→佐西马"式张冠李戴。
-- 改为：本地扫全书抽取"实际出现的叫法清单"，AI 只允许从清单选词分组——
-- AI 从"出题人"变"阅卷人"，译名差异与凭空捏造一起消灭。

local function utf8len(s)
  local _, n = s:gsub("[\228-\233][\128-\191][\128-\191]", "")
  return n
end

-- 常见非人名词过滤（纯功能词；称谓类如"先生/老爷"保留，交给 AI 判断）
local CANDIDATE_STOPWORDS = {
  ["我们"]=true,["他们"]=true,["你们"]=true,["自己"]=true,["什么"]=true,
  ["这个"]=true,["那个"]=true,["没有"]=true,["就是"]=true,["一个"]=true,
  ["一些"]=true,["一样"]=true,["怎么"]=true,["这样"]=true,["那样"]=true,
  ["知道"]=true,["觉得"]=true,["现在"]=true,["时候"]=true,["因为"]=true,
  ["所以"]=true,["但是"]=true,["可是"]=true,["如果"]=true,["虽然"]=true,
  ["而且"]=true,["或者"]=true,["还是"]=true,["只是"]=true,["也是"]=true,
  ["都是"]=true,["不是"]=true,["不能"]=true,["不会"]=true,["可以"]=true,
  ["已经"]=true,["应该"]=true,["可能"]=true,["真的"]=true,["起来"]=true,
  ["出来"]=true,["过来"]=true,["回来"]=true,["一下"]=true,["大家"]=true,
  ["人们"]=true,["他的"]=true,["她的"]=true,["我的"]=true,["你的"]=true,
  ["这里"]=true,["那里"]=true,["哪里"]=true,["这些"]=true,["那些"]=true,
  ["不过"]=true,["然而"]=true,["于是"]=true,["那么"]=true,["怎么"]=true,
}

-- on_progress(done, total)：可选进度回调，用于扫描时刷新提示文字
--
-- v2.0.7：EPUB 直读抽词（不走 crengine 取文）。真机两层实锤（2026-09-25）：
--   ①单点 getTextFromXPointer(页书签) 静默返回 nil（v2.0.5 改区间取文解决）；
--   ②区间取文成功取到 204 万字节，但 cre.cpp 的 getTextFromXPointers /
--     getTextFromPositions 返回文本时一律经 UnicodeToLocal——所有 >0xFF 码点
--     （全部汉字）被硬编码替换成 '?'（KOReader 划线中文变问号同源，上游硬伤），
--     Lua 侧永远拿不到 CJK → 抽词必然为 0。
--   → 改为直接解包 EPUB、Lua 剥 HTML 标签后抽词（与 PC 复现验证路径一致）。
local function utf8Encode(cp)
  if cp < 0x80 then return string.char(cp) end
  if cp < 0x800 then
    return string.char(0xC0 + math.floor(cp / 64), 0x80 + cp % 64)
  end
  if cp < 0x10000 then
    return string.char(0xE0 + math.floor(cp / 4096), 0x80 + math.floor(cp / 64) % 64, 0x80 + cp % 64)
  end
  return string.char(0xF0 + math.floor(cp / 262144), 0x80 + math.floor(cp / 4096) % 64,
      0x80 + math.floor(cp / 64) % 64, 0x80 + cp % 64)
end

local function htmlToText(html)
  -- 剥掉 script/style 块与所有标签，还原常见实体
  html = html:gsub("<%s*(script|style)[^>]->.-</%s*%1%s*>", " ")
  html = html:gsub("<[^>]->", " ")
  html = html:gsub("&nbsp;", " "):gsub("&amp;", "&"):gsub("&lt;", "<")
      :gsub("&gt;", ">"):gsub("&quot;", '"'):gsub("&apos;", "'")
  html = html:gsub("&#x([0-9A-Fa-f]+);", function(h) return utf8Encode(tonumber(h, 16) or 63) end)
  html = html:gsub("&#(%d+);", function(d) return utf8Encode(tonumber(d) or 63) end)
  return html
end

local function scanNameCandidates(ui, on_progress)
  local doc = ui.document
  if not (doc and doc.file) then return nil, "未打开书籍。" end
  if not isEpub(doc.file) then
    return nil, "全书扫描仅支持 EPUB（归组替换本身也只作用于 EPUB）。"
  end
  -- 缓存（书文件变化自动失效，与 mention_scan 同策略）
  local file = doc.file
  local scan_cache_dir = cache_dir .. "/names_scan"
  pcall(function() ensureDir(scan_cache_dir) end)
  local cache_file = nil
  if file then
    local attr = lfs.attributes(file)
    if attr then
      cache_file = scan_cache_dir .. "/" .. md5(file .. "|" .. tostring(attr.size or 0) .. "|" .. tostring(attr.modification or 0)):sub(1, 16) .. ".json"
      local f = io.open(cache_file, "r")
      if f then
        local content = f:read("*all")
        f:close()
        local ok, data = pcall(json.decode, content)
        if ok and type(data) == "table" and type(data.candidates) == "table" then
          return data.candidates, nil, true -- true = 来自缓存
        end
      end
    end
  end

  -- 解包直读：unzip 到临时目录，逐个剥 HTML 标签
  local temp_dir = extractEpub(file)
  if not temp_dir then
    return nil, "解压 EPUB 失败（设备上可能缺少 unzip 命令，或文件无法读取）"
  end
  local html_files = {}
  local function collect(dir)
    for entry in lfs.dir(dir) do
      if entry ~= "." and entry ~= ".." then
        local path = dir .. "/" .. entry
        local attr = lfs.attributes(path)
        if attr then
          if attr.mode == "directory" then
            collect(path)
          elseif attr.mode == "file" and (path:match("%.x?html$") or path:match("%.xhtml$")) then
            html_files[#html_files + 1] = path
          end
        end
      end
    end
  end
  collect(temp_dir)
  table.sort(html_files)
  local all_text = {}
  for i, path in ipairs(html_files) do
    local ok, text = pcall(function()
      local f = io.open(path, "r")
      if not f then return nil end
      local html = f:read("*all")
      f:close()
      return htmlToText(html)
    end)
    if ok and type(text) == "string" then
      all_text[#all_text + 1] = text
    end
    if on_progress and i % 10 == 0 then
      pcall(on_progress, i, #html_files)
    end
  end
  if on_progress then pcall(on_progress, #html_files, #html_files) end
  cleanupTempDir(temp_dir)
  local full = table.concat(all_text, "\n")
  all_text = nil
  -- 诊断日志（落 crash.log，可远程核验）
  logger.info("KOAI NameReplace: scan html_files=", #html_files, " chars=", #full)

  -- 抽取 v2.0.8：逐字节流式扫描 + 代码合并（fengari Lua 5.3 实测 2242 候选，
  -- 与 PC Node 复现 2241 互相印证；关键人物 top160 命中 7/7）。
  -- 重要教训：Lua 模式的 (...) 是捕获组、不能加量词——(...)* 的 * 会被当作
  -- 字面星号字符匹配（v2.0.4-2.0.7 的 token_pat 因此永远匹配不到，真机 0 候选）。
  -- 另外 [\80-\xBF]+ 量词跨不过下一个汉字的声母字节，逐字 find 也拼不出多字词，
  -- 所以必须自己按 UTF-8 字节结构流式扫描。
  local DOT = "\194\183" -- · (U+00B7)
  local freq = {}
  local cur, cur_e = nil, nil
  local function flush()
    if cur then
      if utf8len(cur) <= 24 then -- 排除超长误匹配
        freq[cur] = (freq[cur] or 0) + 1
      end
      if cur:find(DOT, 1, true) then
        -- · 全名的各分段单独计数（如 德米特里·费奥多罗维奇 → 德米特里/费奥多罗维奇）
        local tmp = cur:gsub(DOT, "\1")
        for part in tmp:gmatch("[^\1]+") do
          if utf8len(part) >= 2 then
            freq[part] = (freq[part] or 0) + 1
          end
        end
      end
    end
    cur = nil
  end
  local function isLead(b)
    return b and b >= 0xE4 and b <= 0xE9
  end
  local i, n = 1, #full
  while i + 2 <= n do
    local b = full:byte(i)
    if isLead(b) then
      local b2, b3 = full:byte(i + 1), full:byte(i + 2)
      if b2 and b2 >= 0x80 and b2 <= 0xBF and b3 >= 0x80 and b3 <= 0xBF then
        local ch = full:sub(i, i + 2)
        if cur and i == cur_e + 1 then
          -- 相邻汉字：拼进当前词
          cur, cur_e = cur .. ch, i + 2
        else
          flush()
          cur, cur_e = ch, i + 2
        end
        i = i + 3
      else
        flush()
        i = i + 1
      end
    elseif cur and b == 0xC2 and full:byte(i + 1) == 0xB7
        and i == cur_e + 1 and isLead(full:byte(i + 2)) then
      -- 紧跟当前词的 ·，且后面是汉字（前瞻，防句尾 · 污染）：并入当前词
      cur, cur_e = cur .. DOT, i + 1
      i = i + 2
    else
      flush()
      i = i + 1
    end
  end
  flush()
  local n_tokens = 0
  for _ in pairs(freq) do n_tokens = n_tokens + 1 end
  logger.info("KOAI NameReplace: scan tokens_unique=", n_tokens)

  local candidates = {}
  for w, c in pairs(freq) do
    if c >= 2 and not CANDIDATE_STOPWORDS[w] and utf8len(w) >= 2 then
      candidates[#candidates + 1] = { name = w, count = c }
    end
  end
  table.sort(candidates, function(a, b)
    if a.count ~= b.count then return a.count > b.count end
    return a.name < b.name
  end)
  -- 上限 160 条（控制 prompt 体积在 1K token 量级）
  while #candidates > 160 do table.remove(candidates) end
  local out = {}
  for _, c in ipairs(candidates) do out[#out + 1] = c.name end

  logger.info("KOAI NameReplace: scan candidates=", #out)
  if cache_file and #out > 0 then
    local f = io.open(cache_file, "w")
    if f then
      f:write(json.encode({ candidates = out }))
      f:close()
      logger.info("KOAI NameReplace: scan cache written", cache_file)
    else
      logger.warn("KOAI NameReplace: scan cache write failed", cache_file)
    end
  end
  return out, nil, false
end


function NameReplace.showMergeNamesDialog(ui)
  if not (ui and ui.document) then return end
  local original_file = getOriginalFile(ui)
  if not original_file then return end

  -- 收集上下文（全部纯本地读取）：书名/作者、现有别名规则、已有人物卡名
  local book = nil
  pcall(function()
    local Storage = require("companion_storage")
    book = Storage.getBookInfo(ui)
  end)
  local rules = loadRules(ui, original_file)

  local context_lines = {}
  context_lines[#context_lines + 1] = "书名：" .. ((book and book.title) or "未知")
  local authors = (book and book.authors) or ""
  if authors ~= "" then
    context_lines[#context_lines + 1] = "作者：" .. authors
  end
  local rule_desc = {}
  for _, r in ipairs(rules) do
    if r.enabled and r.original ~= "" and r.nick ~= "" then
      rule_desc[#rule_desc + 1] = r.original .. " = " .. r.nick
    end
  end
  if #rule_desc > 0 then
    context_lines[#context_lines + 1] = "用户已设置的别名（原名 = 昵称）：\n" .. table.concat(rule_desc, "；")
  end
  pcall(function()
    local Storage = require("companion_storage")
    local cards = Storage.loadCards(book)
    local names = {}
    for _, c in ipairs(cards.items or {}) do
      if c and c.name then names[#names + 1] = tostring(c.name) end
    end
    if #names > 0 then
      context_lines[#context_lines + 1] = "已有人物卡名字：" .. table.concat(names, "、")
    end
  end)

  local prompt = table.concat(context_lines, "\n")
      .. "\n\n任务：仅从下面清单中挑出人名/称谓类词条，把书中同一人物的不同叫法归为一组"
      .. "（全名、简称、小名、称谓等），用于全书统一人名。"
      .. "\n要求："
      .. "\n1. 只能使用清单中原样的写法，严禁创造清单外的任何叫法；译名变体必须以书内实际写法为准。"
      .. "\n2. 只报告把握很大的组合，宁漏勿错；不确定就不报。"
      .. "\n3. 严禁把不同人物合并；同名不同人必须分开。"
      .. "\n4. 每组给出 canonical（组内最通用的叫法，必须也在清单中）和一句话判断理由。"
      .. "\n5. 最多 8 组，按重要程度排序。没有发现就输出 []。"
      .. "\n\n只输出 JSON 数组，不要任何其他文字，格式："
      .. '\n[{"names":["叫法1","叫法2"],"canonical":"最通用叫法","reason":"一句话理由"}]'

  -- 可刷新的等待提示：大书扫描期间每 50 页更新一次进度文字，
  -- 避免长时间"冻屏"让用户以为死机（e-ink 上局部刷新，闪烁轻微）
  local loading
  local function setLoadingText(t)
    if loading then UIManager:close(loading) end
    loading = InfoMessage:new { text = t, timeout = nil }
    UIManager:show(loading)
    -- 扫描循环是阻塞的，必须强制重绘才能立刻看到新文字
    pcall(function() UIManager:forceRePaint() end)
  end
  setLoadingText("正在解包全书并提取人名候选（大书可能需十几秒，零 token）…")
  UIManager:scheduleIn(0.1, function()
    -- v2.0.7：EPUB 直读抽词（零 token），AI 只做归类不做发明
    local ok_scan, candidates, scan_err, from_cache = pcall(scanNameCandidates, ui, function(done, total)
      setLoadingText(string.format("正在扫描全书提取人名候选… %d/%d 个章节文件（零 token）", done, total))
    end)
    if not ok_scan then
      scan_err = candidates
      candidates = nil
    end
    if not candidates then
      UIManager:close(loading)
      logger.err("KOAI NameReplace", "人名候选扫描失败:", scan_err)
      UIManager:show(InfoMessage:new {
        text = "全书人名扫描失败：\n" .. tostring(scan_err or "未知错误"),
        timeout = 8,
      })
      return
    end

    local ok, result = pcall(function()
      local queryAI = require("ai_query")
      -- 两点关键（v2.0 真机复现实锤）：
      -- ①必须显式禁用思考：deepseek-v4-flash 默认推理且对"只输出 JSON"任务
      --   会推理到 token 耗尽（8192 时推理 8189），content 永远为空 → 归组失败；
      -- ②不设 max_tokens 上限，沿用全局 response_max_tokens。
      return queryAI({
        { role = "system", content = "你是严谨的中文图书人物分析助手，只输出 JSON，且只使用用户提供的清单中的词条。" },
        { role = "user", content = prompt .. "\n\n书中实际出现的叫法清单（按出现频率降序）：\n" .. table.concat(candidates, "、") },
      }, { thinking = { type = "disabled" }, temperature = 0.2 })
    end)
    UIManager:close(loading)
    if not ok then
      logger.err("KOAI NameReplace", "AI 归组失败:", result)
      UIManager:show(InfoMessage:new {
        text = "AI 归组失败：\n" .. tostring(result),
        timeout = 8,
      })
      return
    end
    local groups = parseGroupsFromAI(result)
    if groups and #groups > 0 then
      -- 越界过滤：组内只保留清单中真实存在的写法（含现有规则的原名/昵称），
      -- 不足两人的组整体丢弃——杜绝 AI 凭空发明书里不存在的译名
      local allowed = {}
      for _, w in ipairs(candidates) do allowed[w] = true end
      for _, r in ipairs(rules) do
        allowed[r.original] = true
        allowed[r.nick] = true
      end
      local filtered = {}
      for _, g in ipairs(groups) do
        local kept = {}
        for _, n in ipairs(g.names or {}) do
          if allowed[n] then kept[#kept + 1] = n end
        end
        if #kept >= 2 then
          filtered[#filtered + 1] = { names = kept, canonical = allowed[g.canonical] and g.canonical or kept[1], reason = g.reason or "" }
        end
      end
      groups = filtered
    end
    if not groups or #groups == 0 then
      UIManager:show(InfoMessage:new {
        text = "AI 没有发现可合并的人名组合。\n（可稍后再试，或继续用\"替换人名\"逐个添加）",
        timeout = 6,
      })
      return
    end

    -- v2.0.1 UI 重构：大 MultiInputDialog 在 PW4 上超高、按钮够不着、键盘遮挡——
    -- 改为 ButtonDialog 三选一入口 + 逐组小弹窗向导（每组一框，永不滚动，不自动弹键盘）
    local existing_nick = {}
    for _, r in ipairs(rules) do
      if r.enabled and r.nick ~= "" then existing_nick[r.original] = r.nick end
    end

    -- 保存函数：kept = { { g = 组, nick = 昵称(可空) }, ... }
    local function saveGroups(kept)
      local updated_rules = loadRules(ui, original_file)
      local added = 0
      local summary = {}
      for _, item in ipairs(kept) do
        local g = item.g
        local nick = trim(item.nick or "")
        -- 目标名：填了昵称用昵称；留空则优先组内已有昵称，再用最简（最短）叫法
        local target = nil
        if nick ~= "" then
          target = nick
        else
          for _, n in ipairs(g.names) do
            if existing_nick[n] then target = existing_nick[n] break end
          end
          if not target then
            target = g.canonical ~= "" and g.canonical or g.names[1]
            for _, n in ipairs(g.names) do
              if #n < #target then target = n end
            end
          end
        end
        for _, n in ipairs(g.names) do
          if n ~= target then
            local found = false
            for _, r in ipairs(updated_rules) do
              if r.original == n then
                r.nick = target
                r.enabled = true
                r.pending = true
                found = true
                break
              end
            end
            if not found then
              updated_rules[#updated_rules + 1] = {
                original = n,
                nick = target,
                enabled = true,
                pending = true,
                created = os.time(),
              }
            end
            added = added + 1
          end
        end
        summary[#summary + 1] = table.concat(g.names, "/") .. " → " .. target
      end
      if added == 0 then
        UIManager:show(InfoMessage:new { text = "没有需要合并的组合。", timeout = 4 })
        return
      end
      saveRules(ui, original_file, updated_rules)

      UIManager:show(ConfirmBox:new {
        text = "已建立 " .. added .. " 条替换规则：\n" .. table.concat(summary, "\n")
            .. "\n\n是否立即应用到本书并重载？（替换会直接写进书文件）",
        ok_text = "立即应用",
        cancel_text = "稍后",
        ok_callback = function()
          NameReplace.applyAndReload(ui)
        end,
      })
    end

    -- 全部采纳：所有组直接用自动昵称保存
    local function adoptAll()
      local kept = {}
      for _, g in ipairs(groups) do
        kept[#kept + 1] = { g = g, nick = "" }
      end
      saveGroups(kept)
    end

    -- 逐组向导：每组一个小弹窗（单输入框），采纳/排除/取消，最后统一确认
    local kept, wizard
    local function runGroup(idx)
      if idx > #groups then
        if #kept == 0 then
          UIManager:show(InfoMessage:new { text = "没有采纳任何组，已退出。", timeout = 4 })
          return
        end
        local lines = {}
        for _, it in ipairs(kept) do
          lines[#lines + 1] = it.g.canonical .. " → " .. (trim(it.nick) ~= "" and trim(it.nick) or "（自动昵称）")
        end
        UIManager:show(ConfirmBox:new {
          text = "共采纳 " .. #kept .. " 组：\n" .. table.concat(lines, "\n") .. "\n\n保存这些规则？",
          ok_text = "保存",
          cancel_text = "放弃",
          ok_callback = function() saveGroups(kept) end,
        })
        return
      end
      local g = groups[idx]
      local prefill = ""
      for _, n in ipairs(g.names) do
        if existing_nick[n] then prefill = existing_nick[n] break end
      end
      local dialog
      dialog = MultiInputDialog:new {
        title = ("第 %d/%d 组：%s"):format(idx, #groups, g.canonical),
        fields = {
          { text = prefill, hint = "昵称（留空＝自动用最简叫法）" },
        },
        buttons = {
          {
            {
              text = "取消全部",
              callback = function()
                UIManager:close(dialog)
              end,
            },
            {
              text = "排除此组",
              callback = function()
                UIManager:close(dialog)
                runGroup(idx + 1)
              end,
            },
            {
              text = "采纳并下一组",
              is_enter_default = true,
              callback = function()
                UIManager:close(dialog)
                kept[#kept + 1] = { g = g, nick = dialog:getFields()[1] or "" }
                runGroup(idx + 1)
              end,
            },
          },
        },
      }
      UIManager:show(dialog)
      -- 不自动弹键盘：先看清整组内容和按钮，点输入框再出键盘（避免键盘遮挡）
    end

    -- 入口：三选一（ButtonDialog 按钮网格，不会超高）
    local entry
    entry = ButtonDialog:new {
      title = "AI 发现 " .. #groups .. " 组同人物叫法",
      buttons = {
        {
          {
            text = "全部采纳（昵称自动）",
            callback = function()
              UIManager:close(entry)
              adoptAll()
            end,
          },
        },
        {
          {
            text = "逐组确认（可填昵称/排除）",
            callback = function()
              UIManager:close(entry)
              kept = {}
              runGroup(1)
            end,
          },
        },
        {
          {
            text = "取消",
            callback = function()
              UIManager:close(entry)
            end,
          },
        },
      },
    }
    UIManager:show(entry)
  end)
end

-- ============ v1.37：卡片显示映射（仅显示层，不改卡片存储） ============

function NameReplace.mapDisplayNames(ui, text)
  if type(text) ~= "string" or text == "" then return text end
  local original_file = getOriginalFile(ui)
  if not original_file then return text end
  local rules = loadRules(ui, original_file)
  for _, r in ipairs(rules) do
    if r.enabled and r.original ~= "" and r.nick ~= "" and r.original ~= r.nick then
      local ok, res = pcall(function()
        return (text:gsub(escapePattern(r.original), escapeReplacement(r.nick)))
      end)
      if ok then text = res end
    end
  end
  return text
end

-- ============ 菜单 ============

-- v2.0.9：规则改动后的统一生效引导（替代已删除的"替换生效"菜单）
-- EPUB：询问是否立即重新生成替换版并重载；非 EPUB：仅提示（AI 回答仍用昵称）
local function offerApplyAfterRuleChange(ui, original_file)
  if isEpub(original_file) then
    UIManager:show(ConfirmBox:new {
      text = "替换规则已更新。\n\n是否立即应用到本书并重载？（大书约需几十秒）",
      ok_text = "立即应用",
      cancel_text = "暂不",
      ok_callback = function()
        NameReplace.applyAndReload(ui)
      end,
    })
  else
    UIManager:show(InfoMessage:new {
      text = "替换规则已更新（该书非 EPUB，不影响正文，仅影响 KOAI 的 AI 回答中的称呼）。",
      timeout = 5,
    })
  end
end

local function buildRulesList(ui)
  local original_file = getOriginalFile(ui)
  if not original_file then
    return { { text = "（未打开书籍）" } }
  end
  local rules = loadRules(ui, original_file)
  if #rules == 0 then
    return {
      {
        text = "（暂无别名。长按划词选\"替换人名\"，或点\"添加人物别名\"）",
      },
    }
  end

  -- v1.38：按人物（昵称）分组——一次合并会产生多条规则（各变体 → 同一昵称）
  local persons, order = {}, {}
  for _, rule in ipairs(rules) do
    local key = rule.nick ~= "" and rule.nick or rule.original
    if not persons[key] then
      persons[key] = { nick = key, rules = {} }
      order[#order + 1] = key
    end
    table.insert(persons[key].rules, rule)
  end

  local items = {}
  for _, key in ipairs(order) do
    local person = persons[key]
    local originals = {}
    for _, r in ipairs(person.rules) do
      if r.original ~= person.nick then originals[#originals + 1] = r.original end
    end
    local sub_items = {
      {
        -- 一键暂停/恢复该人物全部别名（规则保留/重新启用）
        text_func = function()
          local any_enabled = false
          for _, r in ipairs(person.rules) do
            if r.enabled then any_enabled = true break end
          end
          return any_enabled and "暂停替换此人物（规则保留，可恢复）" or "恢复替换此人物"
        end,
        callback = function()
          local rules_now = loadRules(ui, original_file)
          local target_keys = {}
          for _, r in ipairs(person.rules) do target_keys[r.original] = true end
          local any_enabled = false
          for _, r in ipairs(rules_now) do
            if target_keys[r.original] and r.enabled then any_enabled = true break end
          end
          for _, r in ipairs(rules_now) do
            if target_keys[r.original] then
              r.enabled = not any_enabled
              r.pending = true
            end
          end
          saveRules(ui, original_file, rules_now)
          offerApplyAfterRuleChange(ui, original_file)
        end,
      },
      {
        -- v1.38：规则层面的撤销按人物进行
        text = "删除此人物全部别名",
        callback = function()
          -- v2.7.5：提示语随规则状态变化（停用规则未写入正文，删除无需重载）
          local any_enabled_in_person = false
          for _, r in ipairs(person.rules) do
            if r.enabled then any_enabled_in_person = true break end
          end
          UIManager:show(ConfirmBox:new {
            text = "删除「" .. person.nick .. "」的全部别名？\n"
                .. "涉及原名：" .. table.concat(originals, "、")
                .. (any_enabled_in_person
                    and "\n\n删除后可点\"立即应用\"重载：此人名自动恢复原文，"
                        .. "其他人物的替换不受影响（应用时从原书备份重建）。"
                    or  "\n\n该人物的规则均为停用状态，正文本就未替换，删除后无需重新应用。"),
            ok_text = "删除",
            ok_callback = function()
              local rules_now = loadRules(ui, original_file)
              local removed_keys = {}
              for _, r in ipairs(person.rules) do removed_keys[r.original] = true end
              -- v2.7.5：以落盘时的实时状态判定（菜单快照可能过期）；
              -- 仅删除启用中的规则才需要重建应用，停用规则未写入正文，删除不改变书文件
              local any_enabled = false
              for _, r in ipairs(rules_now) do
                if removed_keys[r.original] and r.enabled then any_enabled = true break end
              end
              local kept = {}
              for _, r in ipairs(rules_now) do
                if not removed_keys[r.original] then table.insert(kept, r) end
              end
              saveRules(ui, original_file, kept)
              if any_enabled then
                offerApplyAfterRuleChange(ui, original_file)
              end
            end,
          })
        end,
      },
    }
    -- 逐条规则（微调场景：个别变体单独启停/删除）
    for _, rule in ipairs(person.rules) do
      table.insert(sub_items, {
        text_func = function()
          return (rule.enabled and "[启用] " or "[停用] ")
              .. rule.original .. " → " .. rule.nick
        end,
        enabled = rule.original ~= person.nick, -- 目标名自身无替换规则，防呆
        sub_item_table = {
          {
            text_func = function()
              return rule.enabled and "停用这一条" or "启用这一条"
            end,
            callback = function()
              local rules_now = loadRules(ui, original_file)
              for _, r in ipairs(rules_now) do
                if r.original == rule.original then
                  r.enabled = not r.enabled
                  r.pending = true -- v1.37：改动待生效
                end
              end
              saveRules(ui, original_file, rules_now)
              offerApplyAfterRuleChange(ui, original_file)
            end,
          },
          {
            text = "删除这一条",
            callback = function()
              UIManager:show(ConfirmBox:new {
                text = rule.enabled
                    and ("删除别名：\n" .. rule.original .. " → " .. rule.nick
                        .. "\n\n删除后可点\"立即应用\"重载：该叫法恢复原文，"
                        .. "其他替换不受影响（应用时从原书备份重建）。")
                    or  ("删除别名：\n" .. rule.original .. " → " .. rule.nick
                        .. "\n\n该规则当前为停用状态，正文本就未替换，删除后无需重新应用。"),
                ok_text = "删除",
                ok_callback = function()
                  local rules_now = loadRules(ui, original_file)
                  logger.info("KOAI NameReplace: delete-one requested original=", tostring(rule.original),
                    " rules_now=", #rules_now, " curDoc=", tostring(isCurrentDocument(ui, original_file)))
                  local was_enabled = false
                  local kept = {}
                  for _, r in ipairs(rules_now) do
                    if r.original == rule.original then
                      was_enabled = r.enabled -- v2.7.5：实时状态判定
                    else
                      table.insert(kept, r)
                    end
                  end
                  saveRules(ui, original_file, kept)
                  if was_enabled then
                    -- v2.7.5：仅删除启用中的规则才需要重建应用；停用规则未写入正文
                    offerApplyAfterRuleChange(ui, original_file)
                  end
                end,
              })
            end,
          },
        },
      })
    end
    table.insert(items, {
      text_func = function()
        return person.nick .. "（原名：" .. (table.concat(originals, "、") ~= "" and table.concat(originals, "、") or "无") .. "）"
      end,
      sub_item_table = sub_items,
    })
  end
  return items
end

function NameReplace.getMenuItems(ui)
  return {
    {
      text = "添加人物别名",
      callback = function()
        NameReplace.showAddRuleDialog(ui, "")
      end,
    },
    {
      -- v1.37：AI 人名归组（仅精读模式）
      text = "合并重复人物名（AI 归组，精读）",
      enabled_func = function()
        return isPowerModeLocal() and ui ~= nil and ui.document ~= nil
      end,
      callback = function()
        NameReplace.showMergeNamesDialog(ui)
      end,
    },
    {
      text = "别名列表（按人物分组）",
      sub_item_table_func = function()
        return buildRulesList(ui)
      end,
    },
    {
      text = "还原本书（从自动备份恢复）",
      enabled_func = function()
        return NameReplace.canRestore(ui) or NameReplace.isViewingCache(ui)
      end,
      callback = function()
        NameReplace.revertToOriginal(ui)
      end,
    },
  }
end

-- ============ 划词入口 ============

function NameReplace.registerHighlightButton(koai)
  if not (koai.ui and koai.ui.highlight and koai.ui.highlight.addToHighlightDialog) then
    logger.warn("KOAI NameReplace", "划词入口注册失败：ui.highlight 不可用")
    return
  end
  -- 键名决定划词菜单渲染顺序（orderedPairs 字典序）：
  -- koaireader_card（人物／典故）< koaireader_merge（合并重复人名，仅精读）
  -- < koaireader_namereplace（替换人名，普通模式也可用）——两个新入口都紧挨人物／典故
  koai.ui.highlight:addToHighlightDialog("koaireader_merge", function(reader_highlight)
    return {
      text = "合并重复人名",
      enabled = true,
      show_in_highlight_dialog_func = function()
        return isPowerModeLocal() and koai.ui ~= nil and koai.ui.document ~= nil
      end,
      callback = function()
        if reader_highlight.onClose then
          pcall(function() reader_highlight:onClose() end)
        end
        UIManager:nextTick(function()
          NameReplace.showMergeNamesDialog(koai.ui)
        end)
      end,
    }
  end)
  koai.ui.highlight:addToHighlightDialog("koaireader_namereplace", function(reader_highlight)
    return {
      text = "替换人名",
      enabled = true,
      show_in_highlight_dialog_func = function()
        return true
      end,
      callback = function()
        local selected_text = ""
        if reader_highlight.selected_text and reader_highlight.selected_text.text then
          selected_text = reader_highlight.selected_text.text
        end
        if reader_highlight.onClose then
          pcall(function() reader_highlight:onClose() end)
        end
        UIManager:nextTick(function()
          NameReplace.showAddRuleDialog(koai.ui, selected_text)
        end)
      end,
    }
  end)
end

-- ============ v2.0：对外提供人物名清单（原名+昵称），供全文提及扫描用 ============

function NameReplace.getPersonNames(ui, add)
  if type(add) ~= "function" then return end
  local original_file = getOriginalFile(ui)
  if not original_file then return end
  for _, r in ipairs(loadRules(ui, original_file)) do
    add(r.original)
    add(r.nick)
  end
end

-- v2.0.11：按人物分组提供（昵称 + 该人物全部叫法），供全文提及统一检索。
-- v2.0.11 修复（真机实证）：同一个人的叫法会分散在多条规则里——先归组设昵称 A，
-- 后又用"替换人名"把其中某个叫法改成昵称 B，组与组通过共享叫法连通。
-- 旧实现按昵称机械分组 → 同一人出现两个条目（阿辽沙(7) + 卡老三(2)）。
-- 现用并查集做传递合并：凡共享任何叫法的组自动并成一组；
-- 显示名取最新一条规则的昵称（与书里最后一次实际替换后的名字一致）。
function NameReplace.getPersonGroups(ui, add)
  if type(add) ~= "function" then return end
  local original_file = getOriginalFile(ui)
  if not original_file then return end
  local rules = loadRules(ui, original_file)

  -- pass1：并查集连通（每条规则把 昵称key 与 原名 连起来）
  local parent = {}
  local function find(x)
    if not parent[x] then parent[x] = x end
    while parent[x] ~= x do
      parent[x] = parent[parent[x]]
      x = parent[x]
    end
    return x
  end
  local function union(a, b)
    local ra, rb = find(a), find(b)
    if ra ~= rb then parent[rb] = ra end
  end
  for _, r in ipairs(rules) do
    local nick = trim(tostring(r.nick or ""))
    local orig = trim(tostring(r.original or ""))
    if orig ~= "" then
      union(nick ~= "" and nick or orig, orig)
    end
  end

  -- pass2：显示名 = 该组内最后一条带昵称规则的昵称（后改的赢）
  local display = {}
  for _, r in ipairs(rules) do
    local nick = trim(tostring(r.nick or ""))
    local orig = trim(tostring(r.original or ""))
    if orig ~= "" and nick ~= "" then
      display[find(orig)] = nick
    end
  end

  -- pass3：收集每组全部叫法（原名 + 昵称都算，扫描时都能命中）
  local names, order = {}, {}
  local group_rules = {}
  -- v2.7.5：读"替换生效签名"，判断各组的昵称是否已写进书文件。
  -- 签名 = 最近一次 applyAndReload 成功时的全部启用规则（original\1nick）。
  -- 组内每条规则都 ①启用 ②非待生效 ③在签名里 → 该组昵称已在书文件中，
  -- 全文提及扫描即可只检索昵称、免查老叫法（老叫法在书里已不存在）。
  local applied_set = {}
  local applied_sig = loadRules(ui, original_file, APPLIED_KEY)
  if type(applied_sig) == "string" then
    for item in applied_sig:gmatch("[^\3]+") do
      applied_set[item] = true
    end
  end
  for _, r in ipairs(rules) do
    local nick = trim(tostring(r.nick or ""))
    local orig = trim(tostring(r.original or ""))
    if orig ~= "" then
      local root = find(nick ~= "" and nick or orig)
      if not names[root] then
        names[root] = {}
        order[#order + 1] = root
        group_rules[root] = {}
      end
      local list = names[root]
      local function push(n)
        if n == "" then return end
        for _, x in ipairs(list) do
          if x == n then return end
        end
        list[#list + 1] = n
      end
      push(orig)
      push(nick)
      group_rules[root][#group_rules[root] + 1] = r
    end
  end

  for _, root in ipairs(order) do
    local list = names[root]
    local all_applied = false
    local grs = group_rules[root]
    if type(grs) == "table" and #grs > 0 then
      all_applied = true
      for _, r in ipairs(grs) do
        if not r.enabled or r.pending
            or not applied_set[tostring(r.original or "") .. "\1" .. tostring(r.nick or "")] then
          all_applied = false
          break
        end
      end
    end
    add({
      nick = display[root] or list[1],
      originals = list,
      applied = all_applied,
    })
  end
end

return NameReplace
