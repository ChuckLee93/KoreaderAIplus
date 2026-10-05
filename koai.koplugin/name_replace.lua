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
-- v2.7.5 方案 A：负样本反馈——硬证据否决记录持久化键。走 DocSettings 侧车
-- （与别名规则同生命周期：重扫/重应用/书文件 mtime 变化都不丢）；
-- "删除所有人物全部别名"只清规则不清它——否决知识属于这本书对 AI 行为的
-- 修正，误拦最坏后果也只是"该组合不再被 AI 提名"（等于回到没合并的原状）。
local VETO_KEY = "koai_name_veto"
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
  if isCurrentDocument(ui, original_file) and ui.doc_settings then
    ui.doc_settings:saveSetting(key, rules)
    pcall(function() ui.doc_settings:flush() end)
    return
  end
  local ok, settings = pcall(function() return DocSettings:open(original_file) end)
  if not ok or not settings then return end
  settings:saveSetting(key, rules)
  pcall(function() settings:flush() end)
end

-- ============ 负样本反馈（v2.7.5 方案 A：越用越准） ============
-- 硬证据否决过的分组持久化（DocSettings 侧车，复用规则读写机制换键），
-- 下轮 AI 归组拼进 prompt："上轮被拦的组这轮别再提"。
-- 动机（卡拉马佐夫实锤）：AI 惯性采样——费尧多罗维奇混入老卡组连续两轮
-- 被 V5 拦，temp=0.2 每轮重掷同一枚骰，不回喂则每轮重付学费
-- （否决记录原本只进 crash.log，AI 与用户都看不见）。
local VETO_MAX = 20

local function loadVetoNotes(ui, original_file)
  local notes = loadRules(ui, original_file, VETO_KEY)
  if type(notes) ~= "table" then return {} end
  return notes
end

-- 否决说明形如「否决[a/b/c] 原因」；按组名去重（同组换对叫法再拦不算新知识）
local function vetoGroupToken(note)
  if type(note) ~= "string" then return nil end
  return note:match("^(否决%[[^%]]*%])")
end

local function saveVetoFeedback(ui, original_file, new_notes)
  if type(new_notes) ~= "table" or #new_notes == 0 then return end
  local notes = loadVetoNotes(ui, original_file)
  local seen = {}
  for _, n in ipairs(notes) do seen[vetoGroupToken(n) or n] = true end
  for _, n in ipairs(new_notes) do
    if type(n) == "string" and n ~= "" and not seen[vetoGroupToken(n) or n] then
      seen[vetoGroupToken(n) or n] = true
      notes[#notes + 1] = n
    end
  end
  while #notes > VETO_MAX do table.remove(notes, 1) end
  saveRules(ui, original_file, notes, VETO_KEY)
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
  -- preFix30（块 A）：解压临时目录从 os.tmpname()（→ /tmp，设备根分区仅 ~149MB）
  -- 改为 cache_dir 下的 tmp/（用户分区 /mnt/us，实测 20GB 空闲）。旧行为在大书
  -- 上必失败：42.7MB 的《战争与和平（套装共四册）》→ "unzip: write: No space left
  -- on device"，而 4.4MB 的书正常。同分区=同容量池，改这里不影响任何既有逻辑。
  ensureDir(cache_dir)
  local tmp_root = cache_dir .. "/tmp"
  ensureDir(tmp_root)
  -- preFix31 修正：只清理"陈旧"残留（修改时间超过 24 小时），绝不动在用的。
  -- 根因（09-29 实机两次闪退）：本函数有三条调用链（生成替换版/扫描候选/取全书
  -- 文本 getBookFullText），而 applyRules 执行中途还会经 getBookFullText **再次**
  -- 进入本函数——旧写法"清空整个 tmp/"会把外层正在使用的解压目录删掉：正文替换
  -- 变 0 个文件、repackageEpub 对已删目录 lfs.dir 直接崩掉 KOReader
  -- （JC 约翰·克里斯朵夫 18:04、Cairo 开罗三部曲 18:06 两次实锤，name_replace.lua:684）。
  -- 旧版 os.tmpname() 各自独立目录互不可见，故从未暴露；改共享目录后必须只删陈旧项。
  if lfs.attributes(tmp_root, "mode") == "directory" then
    local now = os.time()
    for entry in lfs.dir(tmp_root) do
      if entry ~= "." and entry ~= ".." then
        local p = tmp_root .. "/" .. entry
        local a = lfs.attributes(p)
        if a and a.mode == "directory" and (now - (a.modification or 0)) > 86400 then
          os.execute(string.format("rm -rf %q", p))
        end
      end
    end
  end
  local temp_dir = string.format("%s/x%d_%d", tmp_root, os.time(), math.random(100000, 999999))
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

-- preFix20 前邻虚字白名单：这些字作前邻时几乎必然是语法成分（"的卡捷琳娜"、
-- "对德米特里"），直接放行替换；白名单外的前邻字交给组合计数门
-- （「前邻字..裸名」全书出现 ≥2 次才判嵌名）。
local NAME_FILLER_CHARS = {
  ["的"] = true, ["了"] = true, ["把"] = true, ["和"] = true, ["与"] = true,
  ["及"] = true, ["从"] = true, ["对"] = true, ["于"] = true, ["在"] = true,
  ["是"] = true, ["让"] = true, ["向"] = true, ["给"] = true, ["替"] = true,
  ["帮"] = true, ["教"] = true, ["为"] = true, ["这"] = true, ["那"] = true,
  ["即"] = true, ["打"] = true, ["将"] = true, ["又"] = true, ["都"] = true,
  ["被"] = true, ["也"] = true, ["由"] = true,
}

-- preFix20：取 bytepos 前一个 UTF-8 字符（bytepos 为 1-based 字节位置）
local function prevUtf8Char(text, bytepos)
  if bytepos <= 1 then return nil end
  local i = bytepos - 1
  while i > 1 do
    local b = text:byte(i)
    if b < 0x80 or b >= 0xC0 then break end
    i = i - 1
  end
  return text:sub(i, bytepos - 1)
end

-- preFix20 裸名前邻咬伤防线（实机《卡拉马佐夫兄弟》"卡捷琳娜→卡嘉"裸名规则把
-- 译者注释里的历史人名"叶卡捷琳娜"咬成"叶卡嘉"×5：前邻"叶"是汉字非·，旧边界
-- 保护不设防）。裸名是其他更长译名的真子串时，逐位判断会误伤正常语法搭配
-- （"老大德米特里"），故做规则级预计算：仅对不含·的裸名规则，若「前邻字..裸名」
-- 组合串在全书出现 ≥2 次（嵌在固定更长译名内）且前邻字不在虚字白名单，则该
-- 前邻字的匹配位一律跳过保持原文（宁漏勿错：跳过多=替换少=无损害）。
local function buildSkipPrefixes(all_text, bare_names)
  local skip = {}
  for _, n in ipairs(bare_names) do
    -- 第一遍：收集出现位的前邻汉字（3 字节 CJK 基本区，非虚字）
    local seen = {}
    local pos = 1
    while true do
      local p = all_text:find(n, pos, true)
      if not p then break end
      if p > 1 then
        local c = prevUtf8Char(all_text, p)
        -- 前邻只认「真正汉字」：UTF-8 3 字节且首字节 0xE4~0xE9（CJK 统一汉字主体区）。
        -- 全角标点（。，！？“”‘’：—、·等）与弯引号虽同属 3 字节 0xE0~0xEF 区，
        -- 但绝非嵌名前邻——preFix20 首轮实机踩坑：「’。德米特里」句末引号被误收
        -- 入跳过表，导致句末正常位置漏替换（。阿列克塞/。德米特里 等 113 条日志）。
        if c and #c == 3 then
          local b = c:byte(1)
          if b >= 0xE4 and b <= 0xE9 and not NAME_FILLER_CHARS[c] then
            seen[c] = true
          end
        end
      end
      pos = p + #n
    end
    -- 第二遍：组合计数 ≥2 才入跳过表
    for c in pairs(seen) do
      local combo = c .. n
      local k, cnt = 1, 0
      while true do
        local p2 = all_text:find(combo, k, true)
        if not p2 then break end
        cnt = cnt + 1
        k = p2 + #combo
      end
      if cnt >= 2 then
        skip[n] = skip[n] or {}
        skip[n][c] = true
        logger.info("KOAI NameReplace: 裸名前邻保护 - ", combo, "×", cnt, "位不替换")
      end
    end
  end
  return skip
end

-- preFix28 前向声明：同姓歧义闸的"全书多身份"开关（multiRoleOf）经 ambCtx.full
-- 取原书全文，而建造 ambCtx 的 applyRules 定义在 getBookFullText 之前，故此处
-- 提前声明该局部（实现在文件后段，用无 local 的函数定义赋值到此处）。
-- 注：若不上移，applyRules 内引用会解析成从未赋值的全局名（= nil → 调用报错）。
local getBookFullText

-- preFix28：同姓歧义闸（方案 A4）——俄译小说里"父子/一家同姓"极为常见，正文又
-- 绝大多数时候只写姓；裸姓规则的昵称一旦定了子辈之名，指父辈的那些位置就会跟着
-- 被改成子辈名（实机 QR 静静的顿河：利斯特尼茨基 305 处，绝大多数据指儿子叶甫盖尼，
-- 9 处指父亲老将军/老地主——「退役的利斯特尼茨基将军」「地主利斯特尼茨基」
-- 「利斯特尼茨基老爷家」，全被改成叶甫盖尼 → 父被叫成子）。
-- 性质：位置级、只拦不并——被判定的那个位置保持原文（宁可少缩，绝不叫错人），
-- 不新增任何替换点（输出只可能是"原书原文"或"插件简称"，不会冒出第三个人名）。
-- 离线 11 书 17083 个真实替换点重放：拦 93 处（0.54%），顿河 9/9 全救回、误改 0，
-- 唯一被整条锁死者本身是坏规则（JC「奥里维回」）。
-- 五条判据（P1~P4 位置级；P3/P5 另加"全书多身份"开关）：
--   P1 后邻家族词（无条件；允许多字词前隔一个「的/之」）：家族/庄园/老宅/府邸/
--      祖父/曾祖/长辈/老爷子/老太爷/老夫人/老将军/老地主/老东家/老爷
--   P2 后邻紧贴「家」（仅纯姓、不含称谓尾）：「利斯特尼茨基家」
--   P3 后邻「将军/地主」＋多身份开关：「利斯特尼茨基将军」仅当该姓在原书里挂过
--      ≥2 种不同身份（将军+中尉=父子两人）才拦——否则「蒙卡达将军」（本尊就是
--      将军）会被整条锁死（BN 实测 18/18 全废的教训）。
--   P4 前邻紧贴：老/小/姓/地主/父子/退役
--   P5 前 12 字窗口含父辈专属称谓（老将军/老地主/老东家/老太爷/老爷子）＋同一开关。
-- 刻意不收「父亲/爸爸」：QR「利斯特尼茨基从华沙写信给父亲」里裸姓指儿子，收了必误伤。
local AMB_POST_HARD = {
  ["家族"] = true, ["庄园"] = true, ["老宅"] = true, ["府邸"] = true,
  ["祖父"] = true, ["曾祖"] = true, ["长辈"] = true, ["老爷子"] = true,
  ["老太爷"] = true, ["老夫人"] = true, ["老将军"] = true, ["老地主"] = true,
  ["老东家"] = true, ["老爷"] = true,
}
local AMB_POST_ROLE = { ["将军"] = true, ["地主"] = true }
local AMB_PRE_TIGHT = { ["老"] = true, ["小"] = true, ["姓"] = true,
  ["地主"] = true, ["父子"] = true, ["退役"] = true }
local AMB_WIN_ELDER = { ["老将军"] = true, ["老地主"] = true, ["老东家"] = true,
  ["老太爷"] = true, ["老爷子"] = true }
-- 多身份开关用的身份词表（"某姓+身份"在原书里出现过的不同身份 ≥2 种 = 该姓下
-- 至少两个人）。收军衔/爵位/职业中区分度高者；不收 父亲/母亲 这类亲属词。
local AMB_ROLES = { "将军", "中尉", "上尉", "大尉", "少校", "中校", "上校",
  "元帅", "少爷", "老爷", "先生", "地主", "医生", "律师", "神父", "老板",
  "公爵", "伯爵" }
-- 称谓尾表（P2 用）：「利斯特尼茨基先生」是姓+称谓通称，不是"某家家宅"，不拦。
-- 注意：本表与上面几张表统一为「词作 key」的集合形式（strHasAny 按 pairs 的 key 取值）。
local AMB_HON = {
  ["先生"] = true, ["老爷"] = true, ["小姐"] = true, ["太太"] = true,
  ["夫人"] = true, ["少爷"] = true, ["女士"] = true, ["老板"] = true,
  ["大夫"] = true, ["老师"] = true, ["神父"] = true, ["牧师"] = true,
  ["医生"] = true, ["律师"] = true, ["舅舅"] = true, ["公公"] = true,
  ["姑娘"] = true, ["大娘"] = true,
}

-- preFix28：该 original 在原书里挂过 ≥2 种不同身份（= 同姓至少两人）。
-- 全书判定结果按 original 缓存（ambCtx.cache），每条规则最多扫一遍全文。
-- ambCtx.full 缺失（无原书文本）时一律返回 false=不拦（降级安全：宁可漏缩）。
local function multiRoleOf(ambCtx, original)
  if not ambCtx or not ambCtx.full then return false end
  local c = ambCtx.cache[original]
  if c ~= nil then return c end
  local n = 0
  for _, r in ipairs(AMB_ROLES) do
    if ambCtx.full:find(original .. r, 1, true) then n = n + 1 end
  end
  c = (n >= 2)
  ambCtx.cache[original] = c
  return c
end

local function strHasAny(s, tbl)
  for w in pairs(tbl) do
    if s:find(w, 1, true) then return true end
  end
  return false
end

-- preFix28：位置级同姓歧义判定。p/q = 匹配起点/终点（1-based 字节），
-- original = 本次规则原名。返回命中标签（写日志用）或 nil。
local function ambiguityGuard(text, p, q, original, ambCtx)
  -- 后邻窗口：P1/P2/P3 只看紧贴（最多隔一个「的/之」），30 字节=10 字足够
  local a = text:sub(q, q + 29)
  local core = a
  local first = a:sub(1, 3)
  if first == "的" or first == "之" then core = a:sub(4) end
  for w in pairs(AMB_POST_HARD) do
    if core:sub(1, #w) == w then return "后邻家族词:" .. w end
  end
  if first == "家" and not original:find("·", 1, true)
      and not strHasAny(original, AMB_HON) then
    return "后邻紧贴家"
  end
  for w in pairs(AMB_POST_ROLE) do
    if core:sub(1, #w) == w and multiRoleOf(ambCtx, original) then
      return "后邻身份词:" .. w
    end
  end
  -- 前邻紧贴
  for w in pairs(AMB_PRE_TIGHT) do
    if p > #w and text:sub(p - #w, p - 1) == w then
      return "前邻紧贴:" .. w
    end
  end
  -- 前 12 字窗口（36 字节）
  local win = text:sub(math.max(1, p - 36), p - 1)
  for w in pairs(AMB_WIN_ELDER) do
    if win:find(w, 1, true) and multiRoleOf(ambCtx, original) then
      return "前邻父辈称谓:" .. w
    end
  end
  return nil
end

-- 边界保护替换（2026-09-27 用户实机验收："不该留下尾巴的"）：
-- 匹配段前/后紧邻 ·(人名连接符) 时跳过——它嵌在更长的人名内部。
-- 长名优先排序只管"长名有规则"的情形；这里管"长名没进清单没规则"的
-- 情形（三段全名仅 1 次够不着 plain≥2 门槛）：组规则"阿黛拉伊达·
-- 伊万诺夫娜→阿黛拉伊达"命中三段全名"阿黛拉伊达·伊万诺夫娜·米乌索娃"
-- 的前缀，留下"阿黛拉伊达·米乌索娃"残骸。跳过后长名整段原样保留。
-- 用 plain find 循环替代 gsub 模式替换，顺带消除转义类隐患。
-- preFix20 增第四参 skipPfx（该裸名规则的前邻跳过表）：前邻字命中时同样
-- 保持原文——治"叶卡捷琳娜→叶卡嘉"式注释区历史人名咬伤。
-- preFix28 增第五参 ambCtx（同姓歧义上下文，见上）：后邻家族词/身份词或前邻
-- 父辈标记命中时该位置保持原文（父辈不被叫成子辈名）；跳过数写入 ambCtx.hits。
local function replaceWholeName(text, original, nick, skipPfx, ambCtx)
  local olen = #original
  if olen == 0 or nick == original then return text, 0, 0 end
  local out = {}
  local last, pos, count, skipped = 1, 1, 0, 0
  local tlen = #text
  while true do
    local p = text:find(original, pos, true)
    if not p then break end
    local q = p + olen
    local inner = false
    if p > 2 and text:sub(p - 2, p - 1) == "·" then
      inner = true  -- 前邻 ·：是更长人名的尾部（他人同姓全名的尾段同理）
    end
    if not inner and q + 1 <= tlen and text:sub(q, q + 1) == "·" then
      inner = true  -- 后邻 ·：是更长人名的头部
    end
    if not inner and skipPfx and p > 1 then
      local pc = prevUtf8Char(text, p)
      if pc and skipPfx[pc] then
        inner = true  -- 前邻咬伤防线：嵌在「前邻字+裸名」固定更长译名内
      end
    end
    -- preFix28：同姓歧义闸——后邻家族词/身份词、前邻父辈标记命中时保持原文
    if not inner and ambCtx then
      local why = ambiguityGuard(text, p, q, original, ambCtx)
      if why then
        inner = true
        skipped = skipped + 1
        local h = ambCtx.hits[original]
        if not h then h = { n = 0, why = {} }; ambCtx.hits[original] = h end
        h.n = h.n + 1
        h.why[why] = (h.why[why] or 0) + 1
      end
    end
    if not inner then
      out[#out + 1] = text:sub(last, p - 1)
      out[#out + 1] = nick
      last = q
      count = count + 1
    end
    pos = q
  end
  if count == 0 then return text, 0, skipped end
  out[#out + 1] = text:sub(last)
  return table.concat(out), count, skipped
end

local function processHtmlFile(path, rules, skip_map, ambCtx)
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
    local rskip = skip_map and skip_map[rule.original] or nil
    local ok, res, n = pcall(replaceWholeName, new_content, rule.original, rule.nick, rskip, ambCtx)
    if ok and n and n > 0 then
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

local function applyRules(temp_dir, rules, original_file)
  local count = 0
  -- preFix31 护栏：解压目录不存在（异常中断/被清理）时干净退出（0 个文件），
  -- 绝不让 collect 里的 lfs.dir 崩进程；下游 repackageEpub 另有同名护栏兜底。
  if lfs.attributes(temp_dir, "mode") ~= "directory" then
    logger.warn("KOAI NameReplace: temp dir missing, skip replace:", tostring(temp_dir))
    return 0
  end
  -- preFix20：两段式——先收集全部 html 路径，为裸名规则做全书级前邻咬伤
  -- 预计算（拼全书文本统计「前邻字..裸名」组合），再逐文件替换。
  local html_files = {}
  local function collect(dir)
    for entry in lfs.dir(dir) do
      if entry ~= "." and entry ~= ".." then
        local path = dir .. "/" .. entry
        local attr = lfs.attributes(path)
        if attr then
          if attr.mode == "directory" then
            collect(path)
          elseif attr.mode == "file"
              and (path:match("%.x?html$") or path:match("%.xhtml$")) then
            html_files[#html_files + 1] = path
          end
        end
      end
    end
  end
  collect(temp_dir)
  local skip_map = nil
  local bare_names = {}
  for _, r in ipairs(rules) do
    if r.original and r.original ~= "" and not r.original:find("·", 1, true) then
      bare_names[#bare_names + 1] = r.original
    end
  end
  if #bare_names > 0 then
    local parts = {}
    for _, p in ipairs(html_files) do
      local f = io.open(p, "r")
      if f then
        parts[#parts + 1] = "\n" .. (f:read("*all") or "")
        f:close()
      end
    end
    skip_map = buildSkipPrefixes(table.concat(parts), bare_names)
  end
  -- preFix28：同姓歧义闸上下文——全文取「未替换原书」（getBookFullText 已收敛，
  -- 有会话缓存，通常与自愈共用同一份、不额外解包）。无原书文本时 ambCtx=nil，
  -- 闸自然失效=不拦（降级安全）。
  local ambCtx = nil
  do
    local full = getBookFullText(original_file)
    if full then ambCtx = { full = full, cache = {}, hits = {} } end
  end
  for _, path in ipairs(html_files) do
    if processHtmlFile(path, rules, skip_map, ambCtx) then count = count + 1 end
  end
  -- preFix28：同姓歧义保护明细（每条命中的规则一行，便于用户核对）
  if ambCtx then
    for orig, h in pairs(ambCtx.hits) do
      local details = {}
      for w, c in pairs(h.why) do details[#details + 1] = w .. "×" .. c end
      table.sort(details)
      logger.info("KOAI NameReplace: 同姓歧义保护 - ", orig, " 跳过 ", h.n,
        " 处（", table.concat(details, "、"), "）")
    end
  end
  logger.info("KOAI NameReplace: replaced in", count, "html files")
  return count
end

local function repackageEpub(temp_dir, output_path)
  -- preFix31 护栏：目录已不存在时干净失败（上层弹错误提示），绝不让 lfs.dir 崩进程。
  -- 09-29 实机崩溃点即此处对已删目录 dir（JC/Cairo 两次闪退，luajit 退出）。
  if lfs.attributes(temp_dir, "mode") ~= "directory" then
    logger.warn("KOAI NameReplace: temp dir missing, abort repackage:", tostring(temp_dir))
    return false
  end
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
  applyRules(temp_dir, rules, original_file)
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

-- preFix23：毒规则静态判定资产前移——applyAndReload 的应用前自愈需要
-- endsWithResidueVerb / 泛称尾表（在 countWordOccurrences/getBookFullText
-- 定义之前），故从 autoFill 区块（原 1966 行）上移至此。
-- 音译外国人名不会以这些动词字收尾（翻译惯例级不变量）；实机 JD/JC 教训
-- 补 回/问/道/讲——「奥里维回答」被切刀残渣成「奥里维回」混进 AI 组，
-- 替换后 16 处「奥里维答」。宁漏勿错：真名收尾误拦代价=漏建组可手动补。
local RESIDUE_TAIL_CHARS = { ["笑"] = true, ["哭"] = true, ["喊"] = true,
  ["叫"] = true, ["嚷"] = true, ["吼"] = true, ["骂"] = true, ["答"] = true,
  ["说"] = true, ["呼"] = true, ["唤"] = true,
  ["回"] = true, ["问"] = true, ["道"] = true, ["讲"] = true }
local function endsWithResidueVerb(s)
  if #s < 3 then return nil end
  local tail = s:sub(-3)
  local b1 = tail:byte(1)
  if b1 < 0xE4 or b1 > 0xE9 then return nil end
  return RESIDUE_TAIL_CHARS[tail] and tail or nil
end
-- preFix23：泛称尾——「加泰罗尼亚小伙子→梅塞苔丝」张冠李戴实机毒（原书 5 处
-- 全指费尔南）。描述性人称短语不配当叫法，AI 组成员剔除+应用前自愈共用。
local GENERIC_TAILS = { ["小伙子"] = true, ["姑娘"] = true, ["老头"] = true,
  ["老太"] = true, ["少年"] = true, ["少女"] = true, ["孩子"] = true,
  ["小孩"] = true, ["男人"] = true, ["女人"] = true }
local function endsWithGenericTail(s)
  if type(s) ~= "string" then return nil end
  for w in pairs(GENERIC_TAILS) do
    if #s > #w and s:sub(-#w) == w then return w end
  end
  return nil
end
-- preFix23：复姓连接符——原文「夏托—勒诺」被切刀切成 夏托+勒诺 两个伪候选，
-- AI 并组后规则「夏托→勒诺」在复姓内部命中 → 147 处「勒诺—勒诺」。
-- 边界保护只认 ·（2 字节），破折号/连字符不设防，故此处补第 5 类连接符集。
local CONNECTOR_CHARS = { ["—"] = true, ["–"] = true, ["-"] = true, ["－"] = true }

-- preFix27：亲属/配偶称谓尾——「容德雷特大娘」是容德雷特的妻子，不是他本人。
-- AI 组把 A 与「A+称谓尾」并成同一人、且两者共用同一昵称时，妻子在正文里被
-- 改成了丈夫的名字（实机 LS 悲惨世界：容德雷特→德纳 与 容德雷特大娘→德纳，
-- 15 处妻子活生生变成「德纳」，与丈夫同名，读者无从分辨）。
-- 判据必须"同昵称才动手"：JD 基督山「唐格拉尔→银行家」与「唐格拉尔夫人→
-- 男爵夫人」昵称不同=夫妻各叫各的=正确形态，绝不能碰（全库 11 书 264 条规则
-- 反向验证：仅命中 LS 1 例，零误伤）。只拦不并：被判定的叫法保持原文，
-- 仍由 A 自己的规则自然覆盖（「容德雷特大娘」→「德纳大娘」可区分）。
local KIN_SUFFIX = {
  ["大娘"] = true, ["大婶"] = true, ["大妈"] = true, ["大嫂"] = true,
  ["太太"] = true, ["夫人"] = true, ["老婆"] = true, ["婆娘"] = true,
  ["媳妇"] = true, ["妻子"] = true, ["嫂子"] = true, ["婶婶"] = true,
  ["嬷嬷"] = true, ["婆婆"] = true, ["公公"] = true, ["妈妈"] = true,
  ["爸爸"] = true, ["女儿"] = true, ["儿子"] = true, ["父亲"] = true,
  ["母亲"] = true, ["姐姐"] = true, ["妹妹"] = true, ["哥哥"] = true,
  ["弟弟"] = true,
}
local function endsWithKinSuffix(s)
  if type(s) ~= "string" then return nil end
  for w in pairs(KIN_SUFFIX) do
    if #s > #w and s:sub(-#w) == w then return w end
  end
  return nil
end

-- preFix30（块 B3）：类别尾闸——家族分支/爵位等"类别词"收尾的叫法不是具体
-- 人名，AI 把「姓＋类别词」当独立人物建规则，等于把整族/整类改成人名。
-- 实机 r30 用户报：LS 悲惨世界「玛尔丹·维尔加支系 → 玛尔丹」6 处（家族分支
-- 被叫成一个叫玛尔丹的人）、BN 百年孤独「弗朗西斯·德雷克爵士 → 弗朗西斯」2 处。
-- 保守收词：只收确认属"类别而非人称"的词。人称头衔（神父/长老/先生/夫人/
-- 将军/公爵/伯爵…）刻意不收——它们是俄/英/法小说里读者熟悉的正常称呼
-- （KM 帕伊西神父、WPa 安德烈公爵 等），收了等于拆东墙补西墙。
local CATEGORY_TAILS = {
  ["支系"] = true, ["家族"] = true, ["爵士"] = true, ["氏族"] = true,
}
local function endsWithCategoryTail(s)
  if type(s) ~= "string" then return nil end
  for w in pairs(CATEGORY_TAILS) do
    if #s > #w and s:sub(-#w) == w then return w end
  end
  return nil
end

-- preFix24：真名截断闸（方案 B，下游宁漏勿错）——译名被切刀切成半截形后冒充
-- 独立叫法落库，替换时在真名内部命中，把正文咬成残句。实机三毒：
--   SC 双城记 查尔斯·达内→查尔斯内 56 处（规则 查尔斯·达→查尔斯）
--   BN 百年孤独 庇拉尔·特尔内拉→庇拉尔内拉 56 处（规则 庇拉尔·特尔→庇拉尔）
--   AK 安娜 谢尔盖·伊万内奇→科兹内奇 23 处（规则 谢尔盖·伊万→科兹）
-- 判据（离线 9 书 222 条现役规则反向验证：命中 3 毒 + 1 次优，零误伤）：
--   A 原书出现 ≥3 次，且 A 后面紧跟的汉字高度集中（≥70%）在同一个字 c，
--   c 既不是功能虚字、也不是称谓首字/卷册字，且延长形 A+c 也 ≥3 次
--   → A 判"更长固定串的碎片"，建 A→昵称 必咬真名，拒建/停用（只拦不并，
--     真名保持原文；用户仍可在别名列表手动加回）。
-- 卷册字教训（离线验证实锤）：JC「约翰·克里斯多夫卷」被误判成半截名——
-- A 后接固定"卷"是书名卷次而非被切掉的尾巴，必须排除，故收 卷/篇/部/册…。
-- 性质说明：这是"碎片代理信号"，抓的是"A 几乎总跟着同一个字"，不等于
-- "A 被某个切字切断"——AK 谢尔盖·伊万命中靠后接「诺」92%（伊万诺维奇），
-- 而真毒发形态「内奇」只占 8%，故提示语一律写"疑似半截名"而非"内字截断"。
local TRUNC_TAIL_EXCLUDE = {
  -- 功能虚字/助词/代词/高频动词（跟任何人名都可能出现，无区分度）
  ["的"]=true,["了"]=true,["是"]=true,["在"]=true,["和"]=true,["与"]=true,
  ["把"]=true,["被"]=true,["对"]=true,["给"]=true,["说"]=true,["问"]=true,
  ["想"]=true,["见"]=true,["找"]=true,["让"]=true,["叫"]=true,["喊"]=true,
  ["答"]=true,["这"]=true,["那"]=true,["哪"]=true,["却"]=true,["而"]=true,
  ["且"]=true,["或"]=true,["都"]=true,["还"]=true,["很"]=true,["再"]=true,
  ["只"]=true,["便"]=true,["就"]=true,["又"]=true,["也"]=true,["跟"]=true,
  ["之"]=true,["其"]=true,["此"]=true,["每"]=true,["各"]=true,["从"]=true,
  ["由"]=true,["但"]=true,["不"]=true,["没"]=true,["要"]=true,["我"]=true,
  ["你"]=true,["他"]=true,["她"]=true,["它"]=true,["咱"]=true,["谁"]=true,
  ["您"]=true,["着"]=true,["过"]=true,["去"]=true,["上"]=true,["时"]=true,
  ["当"]=true,["以"]=true,["至"]=true,["自"]=true,["因"]=true,["将"]=true,
  ["为"]=true,["替"]=true,["帮"]=true,["遇"]=true,["正"]=true,["请"]=true,
  ["会"]=true,["使"]=true,["一"]=true,["第"]=true,["们"]=true,["等"]=true,
  ["什"]=true,["么"]=true,["吗"]=true,["呢"]=true,["吧"]=true,["嘛"]=true,
  ["嗯"]=true,["呀"]=true,["哦"]=true,["哇"]=true,["太"]=true,["更"]=true,
  ["最"]=true,["挺"]=true,["可"]=true,["故"]=true,["乃"]=true,["竟"]=true,
  ["确"]=true,["像"]=true,["似"]=true,["倘"]=true,["虽"]=true,["则"]=true,
  ["纵"]=true,["所"]=true,["现"]=true,["死"]=true,["看"]=true,["听"]=true,
  ["走"]=true,["笑"]=true,["哭"]=true,["活"]=true,["坐"]=true,["吃"]=true,
  ["喝"]=true,["做"]=true,["拿"]=true,["长"]=true,["父"]=true,["神"]=true,
  -- 称谓/职业/爵位首字（A 后接称谓 = 原文"姓+称谓"通称，不是被切掉的尾巴）
  ["先"]=true,["女"]=true,["大"]=true,["小"]=true,["老"]=true,["少"]=true,
  ["中"]=true,["军"]=true,["医"]=true,["护"]=true,["谢"]=true,["帕"]=true,
  ["贝"]=true,["乌"]=true,["艾"]=true,["阿"]=true,["管"]=true,["门"]=true,
  ["仆"]=true,["侍"]=true,["修"]=true,["娘"]=true,["婶"]=true,["爷"]=true,
  ["奶"]=true,["爵"]=true,["伯"]=true,["子"]=true,["男"]=true,["公"]=true,
  ["侯"]=true,["婆"]=true,["哥"]=true,["弟"]=true,["姐"]=true,["妹"]=true,
  ["兄"]=true,["夫"]=true,["君"]=true,["妈"]=true,["爸"]=true,
  -- 卷册/书名用字（JC「约翰·克里斯多夫卷」误判实锤）
  ["卷"]=true,["篇"]=true,["部"]=true,["册"]=true,["集"]=true,["辑"]=true,
  ["章"]=true,["节"]=true,["回"]=true,["页"]=true,
}

-- 前向声明：sanitizePoisonRules（应用前自愈）在 688 行附近定义，但复用
-- 1581 行的 countWordOccurrences（复姓连写判定需要全文计数）。
-- preFix24：截断闸还需逐位置看后继字，故补 truncationSuspect 的前向声明
-- （其实现在 1780 行附近，用无 local 的函数定义赋值到此处）。
-- preFix28：getBookFullText 的声明已上移至 applyRules 之前（同姓歧义闸需要）。
local countWordOccurrences
local truncationSuspect
-- preFix32：短语/称谓守卫（定义在 isPatronymicLoose 之后，前向声明供
-- sanitizePoisonRules 自愈调用）。
local ruleGuardSuspect

-- ============ 防串写硬规则（2026-09-27 米哈依尔实机案例） ============
-- 规则甲的昵称恰为规则乙的原名、且两规则昵称不同（= 跨组）时，甲的替换
-- 产物会被乙二次命中：米哈依尔·伊万诺维奇→米哈依尔（甲）又被
-- 米哈依尔→马卡雷奇（乙）改写成马卡雷奇，全书 5 处串写。
-- 乙的原名与甲的昵称同形 = 歧义裸名，禁用乙（裸名保持原文不替换）；
-- 若禁甲则损失更具体的全名归并。同组规则昵称相同天然豁免（r2.nick ==
-- r1.nick），original==nick 的空规则两头排除。纯函数便于 harness 单测；
-- applyAndReload 每次应用前先过一遍并回写 sidecar。
local function sanitizeRuleChains(rules)
  local disabled = {}
  if type(rules) ~= "table" then return disabled end
  for _, r1 in ipairs(rules) do
    if r1.enabled ~= false and type(r1.original) == "string" and type(r1.nick) == "string"
        and r1.original ~= "" and r1.nick ~= "" and r1.nick ~= r1.original then
      for _, r2 in ipairs(rules) do
        if r2 ~= r1 and r2.enabled ~= false
            and r2.original == r1.nick and r2.nick ~= r1.nick
            and r2.original ~= r2.nick then
          r2.enabled = false
          disabled[#disabled + 1] = r2.original .. "→" .. r2.nick
          logger.warn("KOAI NameReplace: 串写链禁用（昵称=他规则原名）:",
            r2.original, "→", r2.nick, "（由", r1.original, "→", r1.nick, "引起）")
        end
      end
    end
  end
  return disabled
end

-- preFix36：昵称砍切闸——target 是 n 挖掉一块的残渣（切点不在 · 分段边界）
-- 时返回 n，否则 nil。实机 WPa 拿破仑→破仑 全书 522 处被啃（「拿」为刀字，
-- 洗刀产出残形「破仑」被 AI 当独立叫法与全名归组）；顿河 葛利高里→葛利、
-- 悲惨 小伽弗洛→伽弗洛、安娜 谢尔盖·伊万诺维奇→谢尔盖·伊万（父称砍半）
-- 同型。合法形态全部放行：·分段昵称（米哈伊尔·伊万→伊万）、逐级前缀组合
-- （A·B·C→A·B）。纯组内比对，无全文开销。
local function subStrCutBlocked(n, target)
  if type(n) ~= "string" or type(target) ~= "string" then return nil end
  if n == "" or target == "" or target == n then return nil end
  if not n:find(target, 1, true) then return nil end
  if n:find("·", 1, true) then
    -- 字节安全切段（与 expandRelatedNames 同款：·(C2 B7) 整体 gsub 成 \1）
    local segs = {}
    local tmp = n:gsub("·", "\1")
    for seg in tmp:gmatch("[^\1]+") do segs[#segs + 1] = seg end
    for _, s in ipairs(segs) do
      if s == target then return nil end       -- 完整段昵称：合法
    end
    for i = 2, #segs - 1 do
      local combo = table.concat(segs, "·", 1, i)
      if combo == target then return nil end   -- 逐级前缀组合：合法
    end
    return n
  end
  return n  -- 无·原名：任何真子串 target 都是砍切残渣
end

-- preFix23：应用前自愈——存量毒规则自动停用（修复不依赖人工确认）。
-- 实机三毒：JC「奥里维回答→奥里维答」16 处（AI 组成员=切刀残渣，动词尾）；
-- JD「夏托—勒诺→勒诺—勒诺」147 处（复姓连写自嵌套）；JD「加泰罗尼亚
-- 小伙子→梅塞苔丝」5 处张冠李戴（泛称尾）。三条判定：
--   (a) 动词尾收尾 → 停用（无需全文）；(b) 泛称尾收尾 → 停用（无需全文）；
--   (c) 原文存在 original<连接符>nick 连写（任一连接符计数>0）→ 停用。
-- 误停用代价=该规则对应叫法保持原文（宁漏勿错），用户可在别名列表手动
-- 重新启用。original_file 传原书路径（getOriginalFile 保证是未替换原书），
-- getBookFullText 带缓存，批量一次解包。
local function sanitizePoisonRules(rules, original_file)
  local disabled = {}
  if type(rules) ~= "table" then return disabled end
  -- preFix36：昵称砍切自愈——昵称是原名挖掉一块的残渣（拿破仑→破仑 522 处
  -- 实锤）。纯比对停用，正文由重建式应用从原书还原（宁漏勿错）。
  for _, r in ipairs(rules) do
    if r.enabled ~= false and type(r.original) == "string" and type(r.nick) == "string"
        and r.original ~= "" and r.nick ~= "" and r.nick ~= r.original
        and subStrCutBlocked(r.original, r.nick) then
      r.enabled = false
      disabled[#disabled + 1] = r.original .. "→" .. r.nick .. "（昵称砍切残渣）"
      logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
        "（昵称是原名挖掉一块的残渣且切点不在分段边界，完整名保持原文宁漏勿错）")
    end
  end
  local needs_text = {}
  for _, r in ipairs(rules) do
    if r.enabled ~= false and type(r.original) == "string" and type(r.nick) == "string"
        and r.original ~= "" and r.nick ~= "" and r.nick ~= r.original then
      local vt = endsWithResidueVerb(r.original)
      local gt = not vt and endsWithGenericTail(r.original) or nil
      if vt then
        r.enabled = false
        disabled[#disabled + 1] = r.original .. "→" .. r.nick .. "（动词尾「" .. vt .. "」残渣）"
        logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
          "（动词尾「" .. vt .. "」，叫法保持原文宁漏勿错）")
      elseif gt then
        r.enabled = false
        disabled[#disabled + 1] = r.original .. "→" .. r.nick .. "（泛称尾「" .. gt .. "」）"
        logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
          "（泛称尾「" .. gt .. "」，描述短语不配当叫法）")
      else
        needs_text[#needs_text + 1] = r
      end
    end
  end
  if #needs_text > 0 and original_file then
    local probes, owner = {}, {}
    for _, r in ipairs(needs_text) do
      for conn in pairs(CONNECTOR_CHARS) do
        local w = r.original .. conn .. r.nick
        probes[#probes + 1] = w
        owner[w] = r
      end
    end
    local ok_c, counts = pcall(countWordOccurrences, original_file, probes)
    if ok_c and counts then
      for _, w in ipairs(probes) do
        local r = owner[w]
        if r and r.enabled ~= false and (counts[w] or 0) > 0 then
          r.enabled = false
          disabled[#disabled + 1] = r.original .. "→" .. r.nick .. "（复姓连写「" .. w .. "」×" .. counts[w] .. "）"
          logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
            "（原文存在复姓连写「" .. w .. "」×" .. counts[w] .. "，原名是复姓前半非独立叫法）")
        end
      end
    end
  end
  -- preFix24：真名截断闸自愈——存量规则的原名若是"更长固定串的碎片"
  -- （实机三毒 查尔斯·达/庇拉尔·特尔/谢尔盖·伊万），停用该条；正文由
  -- 重建式应用自动从原书还原（宁漏勿错：真名保持原文，用户可在别名列表加回）。
  if original_file then
    for _, r in ipairs(rules) do
      if r.enabled ~= false and type(r.original) == "string" and type(r.nick) == "string"
          and r.original ~= "" and r.nick ~= "" and r.nick ~= r.original then
        local ok_t, tc, tn, tot, cnt, ext = pcall(truncationSuspect, original_file, r.original)
        if ok_t and tc then
          r.enabled = false
          disabled[#disabled + 1] = r.original .. "→" .. r.nick
              .. "（疑似半截名：原名 " .. cnt .. " 次中后接「" .. tc .. "」"
              .. tn .. "/" .. tot .. "，延长形 " .. ext .. " 次）"
          logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
            "（疑似半截名「" .. r.original .. tc .. "」，一半的真名被当叫法，"
            .. "叫法保持原文宁漏勿错）")
        end
      end
    end
  end
  -- preFix27：配偶称谓自愈——B = A+亲属称谓尾 且 B 与 A 在本书规则表内共用同一
  -- 昵称，说明 AI 把妻子并进了丈夫的组（实机 LS 悲惨世界：容德雷特大娘→德纳
  -- 与 容德雷特→德纳，妻子被改成了丈夫的名字）。停用 B，正文由重建式应用从
  -- 原书还原（「容德雷特大娘」→「德纳大娘」，仍可区分是德纳家的人）。
  -- JD 基督山 唐格拉尔夫人→男爵夫人 与 唐格拉尔→银行家 昵称不同=正确形态，
  -- 不满足同昵称条件，不受影响。
  do
    local by_orig = {}
    for _, r in ipairs(rules) do
      if r.enabled ~= false and type(r.original) == "string" and r.original ~= ""
          and by_orig[r.original] == nil then
        by_orig[r.original] = r
      end
    end
    for _, r in ipairs(rules) do
      if r.enabled ~= false and type(r.original) == "string" and type(r.nick) == "string"
          and r.original ~= "" and r.nick ~= "" and r.nick ~= r.original then
        local kin = endsWithKinSuffix(r.original)
        if kin then
          local a = r.original:sub(1, #r.original - #kin)
          local ra = a ~= "" and by_orig[a] or nil
          if ra and ra ~= r and type(ra.nick) == "string" and ra.nick == r.nick then
            r.enabled = false
            disabled[#disabled + 1] = r.original .. "→" .. r.nick
                .. "（配偶称谓「" .. kin .. "」，与「" .. a .. "」被改成同一个名字）"
            logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
              "（「" .. a .. "」的亲属称谓，同名会让两个人物混淆，"
              .. "叫法保持原文宁漏勿错）")
          end
        end
      end
    end
  end
  -- preFix32：短语/称谓守卫自愈——存量毒规则（WPa 实锤 12 条：皮埃尔觉得/
  -- 到皮埃尔/安德烈公爵→安德烈/亚历山大皇帝→亚历山大/罗斯托夫家→罗斯托夫/
  -- 安德烈伊奇→安德烈…）自动停用，正文由重建式应用从原书还原。纯字符串
  -- 判据无需全文。
  for _, r in ipairs(rules) do
    if r.enabled ~= false and type(r.original) == "string" and type(r.nick) == "string"
        and r.original ~= "" and r.nick ~= "" and r.nick ~= r.original then
      local gk = ruleGuardSuspect(r.original, r.nick)
      if gk then
        r.enabled = false
        disabled[#disabled + 1] = r.original .. "→" .. r.nick .. "（" .. gk .. "）"
        logger.warn("KOAI NameReplace: 毒规则自愈停用 -", r.original, "→", r.nick,
          "（" .. gk .. "，叫法保持原文宁漏勿错）")
      end
    end
  end
  return disabled
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
  -- 防串写（米哈依尔案例）：昵称 = 他规则原名的规则先禁用再应用，
  -- 并回写 sidecar——别名列表界面同步显示 [停用]，应用路径全覆盖
  --（保存即应用/手动应用/换书重开都从这一处过）。
  local chain_disabled = sanitizeRuleChains(rules)
  if #chain_disabled > 0 then
    logger.warn("KOAI NameReplace: 串写链禁用:", table.concat(chain_disabled, "；"))
    saveRules(ui, original_file, rules)
  end
  -- preFix23：应用前自愈——动词尾/泛称尾/复姓连写毒规则自动停用并回写
  -- sidecar（奥里维回/夏托/加泰罗尼亚小伙子 三实机毒的根治入口）。
  local poison_disabled = sanitizePoisonRules(rules, original_file)
  if #poison_disabled > 0 then
    logger.warn("KOAI NameReplace: 毒规则自愈:", table.concat(poison_disabled, "；"))
    saveRules(ui, original_file, rules)
  end
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
      -- preFix38（2026-09-30）：大书内存降级重试。实锤（战争与和平套装版 42.7MB，
      -- 4 张 10MB 大图）：书开着时渲染占满 PW4 内存，解包子进程启动即失败
      -- （"unzip failed, result: -1" = fork 层失败，无任何 unzip stderr 输出），
      -- 45 秒后阅读器整体重启；原书与备份全程未动。降级策略：借 reloadDocument
      -- 的「关→callback→重开」同步窗口（readerui.lua L940：onClose 后同步执行
      -- callback，完成后才 showReader，无超时）——onClose 释放渲染内存，callback
      -- 内强制 GC 后重试一次；成功则在文档关闭状态下写侧车+换入文件；失败则不
      -- 换入（重开以原文打开，零损失）。小书首试即成功，永不进此分支，体验不变。
      local loading = InfoMessage:new {
        text = "大书内存吃紧，正在关闭书本腾出内存重新处理…\n完成后自动重新打开本书，约一两分钟，请勿操作。",
        timeout = nil,
      }
      UIManager:show(loading)
      pcall(function() UIManager:forceRePaint() end)
      if ui.reloadDocument then
        ui:reloadDocument(function()
          collectgarbage("collect")
          local temp_path2, err2 = processEpub(backup_path, enabled)
          UIManager:close(loading)
          if not temp_path2 then
            logger.warn("KOAI NameReplace: pf38 降级重试仍失败:", tostring(err2))
            UIManager:show(InfoMessage:new {
              text = "重试仍失败（原书未改动，本书将以原文重新打开）：\n" .. tostring(err2)
                  .. "\n可重启阅读器后再点一次应用。",
              timeout = 10,
            })
            return
          end
          -- 文档已关：loadRules/saveRules 自动走磁盘 sidecar（isCurrentDocument=false），
          -- 不会被任何活动会话覆盖（onClose 已完成 doc_settings 的最终 flush）。
          local rules_now = loadRules(ui, original_file)
          local applied_keys2 = {}
          for _, r in ipairs(enabled) do
            applied_keys2[tostring(r.original or "") .. "\1" .. tostring(r.nick or "")] = true
          end
          for _, r in ipairs(rules_now) do
            if applied_keys2[tostring(r.original or "") .. "\1" .. tostring(r.nick or "")] then
              r.pending = nil
            end
          end
          saveRules(ui, original_file, rules_now)
          local sig_items2 = {}
          for _, r in ipairs(enabled) do
            sig_items2[#sig_items2 + 1] = tostring(r.original or "") .. "\1" .. tostring(r.nick or "")
          end
          saveRules(ui, original_file, table.concat(sig_items2, "\3"), APPLIED_KEY)
          if not swapFile(temp_path2, original_file) then
            logger.warn("KOAI NameReplace: pf38 swap file failed", temp_path2, "->", original_file)
          else
            logger.info("KOAI NameReplace: pf38 replaced book file", original_file)
          end
        end)
      else
        -- 极旧 KOReader 无 reloadDocument：维持旧行为（只报错不重试）
        UIManager:show(InfoMessage:new {
          text = "生成替换版失败：\n" .. tostring(err),
          timeout = 8,
        })
      end
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

-- 归组数上限：已取消（2026-09-27 用户拍板"组数没必要设上限"）——组数由书决定。
-- 历史教训一（v2.7.5）：prompt 与解析器上限不同步（prompt 12 组/解析器硬截 8），
--   AI 按重要度排序的第 9~12 组被静默丢弃——实机"还是8组"根因。
-- 历史教训二：12 组上限把佐西马/格里果利/彼得等真实配角挤掉——上限从来不是
--   质量工具（防低质组靠清单验证+宁缺毋滥+称谓/父称防线），砍的反而可能是真组。
-- 防失控正解：解析器残缺 JSON 容错——AI 输出被 max_tokens 截断时（尾部无 ]，
--   原实现在此直接 return nil 整次归组全灭）截到最后一个完整对象补 ] 重试，
--   救回多少组是多少。

-- 残缺 JSON 容错：截到最后一个完整对象的 } 补 ] 后重试
local function salvageJsonArray(s)
  local last = nil
  for k = #s, 1, -1 do
    if s:sub(k, k) == "}" then last = k break end
  end
  if not last then return nil end
  local ok, data = pcall(json.decode, s:sub(1, last) .. "]")
  if ok and type(data) == "table" then return data end
  return nil
end

-- 从 AI 返回文本中提取 JSON 数组并清洗
local function parseGroupsFromAI(text)
  if type(text) ~= "string" then return nil end
  local i = text:find("[", 1, true)
  if not i then return nil end
  local j
  for k = #text, i, -1 do
    if text:sub(k, k) == "]" then j = k break end
  end
  local ok, data
  if j and j > i then
    ok, data = pcall(json.decode, text:sub(i, j))
  end
  if not ok or type(data) ~= "table" then
    -- 截断/畸形容错：从第一个 [ 起截到最后完整 } 补 ] 重试
    data = salvageJsonArray(text:sub(i))
    if data then
      logger.info("KOAI NameReplace: AI 输出疑似被截断/畸形，容错救回组数 =", #data)
    end
  end
  if type(data) ~= "table" then return nil end
  logger.info("KOAI NameReplace: AI 返回原始组数 =", #data)
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
  ["后来"]=true,["最后"]=true,["首先"]=true,["其次"]=true,["突然"]=true,
  ["接着"]=true,
  -- 繁体对应（代词类如"我們/他們"因"們"是切刀自动碎掉，无需列）
  ["這個"]=true,["那個"]=true,["什麼"]=true,["沒有"]=true,["一個"]=true,
  ["知道"]=true,["現在"]=true,["時候"]=true,["因為"]=true,["所以"]=true,
  ["還是"]=true,["這樣"]=true,["那樣"]=true,["已經"]=true,["應該"]=true,
  ["這裡"]=true,["那裡"]=true,["這些"]=true,["那些"]=true,["不過"]=true,
  ["於是"]=true,["後來"]=true,["最後"]=true,["首先"]=true,["其次"]=true,
  ["突然"]=true,["接著"]=true,["覺得"]=true,["怎麼"]=true,["不會"]=true,
  -- v2.7.5 称谓/泛称禁入（实机教训：清单收了"父亲/老头儿"，AI 把它们归进
  -- 费奥多尔组，昵称回退取字节最短 → "费奥多尔·巴甫洛维奇→父亲"，第一章
  -- 标题变"父亲·卡拉马佐夫"。称谓/泛称全书指人不定，绝不能当人物叫法；
  -- 扫描清单与 AI 提名验证两处都拦。家庭称谓在中文书里永远是泛指高频词）
  ["父亲"]=true,["母亲"]=true,["爸爸"]=true,["妈妈"]=true,["儿子"]=true,
  ["女儿"]=true,["哥哥"]=true,["弟弟"]=true,["姐姐"]=true,["妹妹"]=true,
  ["爷爷"]=true,["奶奶"]=true,["外公"]=true,["外婆"]=true,["叔叔"]=true,
  ["伯伯"]=true,["舅舅"]=true,["姑姑"]=true,["婶婶"]=true,["孙子"]=true,
  ["孙女"]=true,["大哥"]=true,["大姐"]=true,["老爷"]=true,["太太"]=true,
  ["夫人"]=true,["小姐"]=true,["少爷"]=true,["大人"]=true,["先生"]=true,
  ["老头儿"]=true,["老头子"]=true,["孩子"]=true,["小孩"]=true,["姑娘"]=true,
  ["小伙子"]=true,["长老"]=true,["诸位"]=true,["个人"]=true,["事情"]=true,
  ["地方"]=true,["今天"]=true,["刚才"]=true,["难道"]=true,["告诉"]=true,
  ["相信"]=true,["明白"]=true,["亲爱"]=true,["完全"]=true,["尽管"]=true,
  ["喜欢"]=true,["回事"]=true,["下子"]=true,["件事"]=true,
  -- scan6："未婚妻"整词拦截 + 作为称谓前缀粘连的匹配源（"未婚妻卡捷琳娜…"）
  ["未婚妻"]=true,
  -- 繁体对应（与简体同形者如事情/地方/完全/相信/明白/孩子/太太/夫人/小姐已含）
  ["父親"]=true,["母親"]=true,["兒子"]=true,["女兒"]=true,["媽媽"]=true,
  ["爺爺"]=true,["老爺"]=true,["少爺"]=true,["老頭兒"]=true,["老頭子"]=true,
  ["嬸嬸"]=true,["孫子"]=true,["孫女"]=true,["小夥子"]=true,["長老"]=true,
  ["諸位"]=true,["個人"]=true,["剛才"]=true,["難道"]=true,["告訴"]=true,
  ["親愛"]=true,["儘管"]=true,["喜歡"]=true,
}

-- v2.7.5 虚字切刀：把高频虚字/代词/助词当"切刀"，专治人名藏串漏计——
-- 中文无分词，"在佐西马长老的灵柩旁"这类长汉字段在旧扫描中整体成词，
-- 藏在中间的人名（佐西马长老/老卡拉马佐夫）频次永远为 0，进不了候选清单。
-- 卡拉马佐夫兄弟实测：格露莘卡 #172→#8、斯乜尔加科夫 #112→#13、
-- 费奥多尔·巴甫洛维奇 #255→#29；"阿辽沙说/我不知道/说真的"类噪声一并消灭。
-- 刀字只收"几乎不可能出现在人名中"的字；刻意排除人名风险字：
-- 道(道森)、向(向忠发)、同(翁同龢)、于(于连)、里(格里果利)、得(彼得)、
-- 哈(音译)、然(浩然)、刚(李刚)、才(才让)、真(淑真)、若(若曦)、来(来俊臣)、
-- 果(格里果利 222 次——2026-09-27 实机教训："如果"拆词把老仆全名切碎，
--   "格里"进 top30 而"格里果利"不在清单，AI 整组无从归起)、
-- 如(婉如/如萍类人名——与"果"同构隐患；"如果/如此/如何"等泛词已移交
--   BIGRAM_KNIFE 二元整词切，scan8)。
local CANDIDATE_KNIFE = {
  ["的"]=true,["了"]=true,["是"]=true,["在"]=true,["和"]=true,["与"]=true,
  ["把"]=true,["被"]=true,["对"]=true,["给"]=true,["说"]=true,["问"]=true,
  ["想"]=true,["见"]=true,["找"]=true,["让"]=true,["叫"]=true,["喊"]=true,
  ["答"]=true,["这"]=true,["那"]=true,["哪"]=true,["却"]=true,["而"]=true,
  ["且"]=true,["或"]=true,["都"]=true,["还"]=true,["很"]=true,["再"]=true,
  ["只"]=true,["便"]=true,["就"]=true,["又"]=true,["也"]=true,["跟"]=true,
  ["之"]=true,["其"]=true,["此"]=true,["每"]=true,["各"]=true,["从"]=true,
  ["由"]=true,["但"]=true,["不"]=true,["没"]=true,
  ["要"]=true,["我"]=true,["你"]=true,["他"]=true,["她"]=true,["它"]=true,
  ["咱"]=true,["谁"]=true,["您"]=true,["着"]=true,["过"]=true,["去"]=true,
  ["上"]=true,["时"]=true,["当"]=true,["以"]=true,["内"]=true,["至"]=true,
  ["自"]=true,["因"]=true,["将"]=true,["为"]=true,["替"]=true,["帮"]=true,
  ["遇"]=true,["正"]=true,["请"]=true,["会"]=true,["使"]=true,["一"]=true,
  ["第"]=true,["们"]=true,["等"]=true,["什"]=true,["么"]=true,["吗"]=true,
  ["呢"]=true,["吧"]=true,["嘛"]=true,["嗯"]=true,["呀"]=true,["哦"]=true,
  ["哇"]=true,["太"]=true,["更"]=true,["最"]=true,["挺"]=true,["可"]=true,
  ["故"]=true,["乃"]=true,["竟"]=true,["确"]=true,["像"]=true,["似"]=true,
  ["倘"]=true,["虽"]=true,["则"]=true,["纵"]=true,["所"]=true,["现"]=true,
  -- 繁体对应（本插件仅服务简繁中文用户）：說問這還從們麼嗎…与简体同效
  ["與"]=true,["對"]=true,["給"]=true,["說"]=true,["問"]=true,["讓"]=true,
  ["見"]=true,["這"]=true,["卻"]=true,["還"]=true,["從"]=true,["沒"]=true,
  ["誰"]=true,["著"]=true,["過"]=true,["時"]=true,["當"]=true,["內"]=true,
  ["將"]=true,["為"]=true,["幫"]=true,["請"]=true,["會"]=true,["們"]=true,
  ["麼"]=true,["嗎"]=true,["確"]=true,["雖"]=true,["則"]=true,["縱"]=true,
  ["現"]=true,["裡"]=true,["裏"]=true,["隻"]=true,["及"]=true,
  -- 高频粘刀动词（0% 人名风险；"老卡拉马佐夫死了"若缺"死"会被粘成"老卡拉马佐夫死"）
  ["死"]=true,["看"]=true,["听"]=true,["走"]=true,["笑"]=true,["哭"]=true,
  ["活"]=true,["坐"]=true,["吃"]=true,["喝"]=true,["做"]=true,["拿"]=true,
  ["聽"]=true,
  -- 2026-09-27 实机教训：称谓尾词不切导致"佐西马长老(62次)/格里果利长老/
  -- 菲拉邦特神父(18次)"整串粘连，本名独立 token 被吃光——佐西马/格里果利
  -- 因此从清单消失、AI 无法归组。切"长/父/神"后人名部分独立成词。
  -- 人名风险评估：长（长孙复姓/李长歌类，本书无）、父/神（人名几乎不用）。
  ["长"]=true,["父"]=true,["神"]=true,
}

-- 二元泛词切刀（scan8 新增）：高频泛词整词切，根治单字刀"果"式死结。
-- 教训：为拆"如果"收单字"果"，把"格里果利"（222 次）切成"格里"+"果利"；
-- 同构隐患"如"（婉如/如萍是人名）。方案：这些高频泛字退出单字刀，
-- 其泛词组合在双字层整词切——泛词切得干净，人名用字永不出刀。
-- 只需覆盖 count 可能进 top160（≥40 次）的组合；低频"果X/如X"组合
-- 连 2 字门槛都够不着，回流无害。
local BIGRAM_KNIFE = {
  -- 果系
  ["如果"]=true,["结果"]=true,["果然"]=true,["果真"]=true,["后果"]=true,
  ["效果"]=true,["成果"]=true,["因果"]=true,["苹果"]=true,["糖果"]=true,
  ["果子"]=true,["果敢"]=true,["果断"]=true,
  -- 如系
  ["如此"]=true,["如何"]=true,["比如"]=true,["例如"]=true,["假如"]=true,
  ["犹如"]=true,["譬如"]=true,["一如"]=true,["如同"]=true,["如实"]=true,
  ["如下"]=true,["如上"]=true,["如愿"]=true,["如常"]=true,["如期"]=true,
  -- 称谓整词切：单字刀"父/长"会拆"父亲/长老"使粘连串换头漏网
  -- （实机教训："亲费奥多尔·巴甫洛维奇"——"父"切后"亲"打头绕过前缀检查）
  ["父亲"]=true,["母亲"]=true,["儿子"]=true,["女儿"]=true,["老仆"]=true,
  -- 繁体对应（简繁同形词已含在上两行，此处补特有字形）
  ["結果"]=true,["後果"]=true,["蘋果"]=true,
}

-- 长词新档首尾洗刀扩充表（2026-09-27，配合三档长词通道）：
-- 三档新档（≥8字≥2次 / 6~7字≥8次）全量复算实证：136 净增词过半是
-- "伊万·费奥多罗维奇勃然大怒"（粘尾）、"到卡捷琳娜·伊万诺夫娜"（带头）类噪声。
-- 洗刀逻辑：候选串首字命中 HEAD_KNIFE_EXTRA 或末字命中 TAIL_KNIFE_EXTRA 即拒收
-- （仅作用于 ≥6 字新档；top160 与 4~5 字老档不洗，防"彼得/华生"类误杀回归）。
-- CANDIDATE_KNIFE 刻意排除的人名风险字（道/向/同/于/里/得/哈/然/刚/才/真/若/来）
-- 在中部出现合法（格里果利/彼得/道森），但首尾出现即整个人名串不成立，故入尾刀。
-- 注意："老/父"只入尾刀不入首刀——"老卡拉马佐夫"首字是"老"，必须保留。
local HEAD_KNIFE_EXTRA = {
  ["白"]=true,["地"]=true,["位"]=true,["个"]=true,["怕"]=true,["指"]=true,
  ["面"]=true,["访"]=true,["仆"]=true,["令"]=true,["次"]=true,["弟"]=true,
  ["依"]=true,["担"]=true,["妻"]=true,["两"]=true,["到"]=true,
  -- 二轮复算补充（6+ 字首位置无合法人名；"于连/利玛窦"等 2~3 字不受影响，
  -- 它们走 top160 与 4~5 字老档）：
  ["未"]=true,["家"]=true,["长"]=true,["二"]=true,["利"]=true,
  ["于"]=true,["圣"]=true,
  -- 2026-09-27 脏书实机教训（倒置规则污染书文本后扫描粘出"带到彼得·
  -- 伊里奇/有格里果利·瓦西里耶维奇/向卡捷琳娜·伊万诺夫娜"）：
  ["有"]=true,["带"]=true,["向"]=true,
  -- 2026-09-27 二轮实机教训（卡拉马佐夫）：流式切刀"长"（长老教训必需）把
  -- "长子德米特里·费奥多罗维奇"切出残尾"子德米特里·费奥多罗维奇"——9 字
  -- 2 次恰过 ≥8 字档门槛入清单，AI 顺手收编进大儿子组，V4 连坐整组否决
  -- （米嘉 1136 次陪葬）。6+ 字串首字"子"只可能是切刀残尾（中文人名不以
  -- "子"开头），入首刀；4~5 字残尾另见 isKinResidueHead。
  ["子"]=true,
}
local TAIL_KNIFE_EXTRA = {
  ["续"]=true,["微"]=true,["重"]=true,["怒"]=true,["作"]=true,["声"]=true,
  ["爱"]=true,["人"]=true,["天"]=true,["样"]=true,["语"]=true,["久"]=true,
  ["取"]=true,["家"]=true,["马"]=true,["长"]=true,["平"]=true,["录"]=true,
  ["任"]=true,["饼"]=true,["栈"]=true,["站"]=true,["立"]=true,["到"]=true,
  ["出"]=true,["乎"]=true,["总"]=true,["经"]=true,["已"]=true,["回"]=true,
  ["毫"]=true,["乐"]=true,["生"]=true,["姐"]=true,["父"]=true,["老"]=true,
  ["道"]=true,["向"]=true,["同"]=true,["于"]=true,["里"]=true,["得"]=true,
  ["哈"]=true,["然"]=true,["刚"]=true,["才"]=true,["真"]=true,["若"]=true,
  ["来"]=true,
  -- 二轮复算补充（6+ 字尾位置无合法人名）：
  ["地"]=true,["干"]=true,["脸"]=true,["记"]=true,
  -- 2026-09-27 脏书实机教训：扫描粘刀产物"伊万诺夫娜末/卡拉马佐夫据"
  -- （"…伊万诺夫娜末了/…卡拉马佐夫据说"粘尾）。6+ 字尾位置无合法人名，
  -- 且 末吉/末雄 类 2 字日名走老档不受影响。
  ["末"]=true,["据"]=true,
}

-- 运行时合并：首刀/尾刀 = CANDIDATE_KNIFE 全集 ∪ 各自扩充
local HEAD_KNIFE, TAIL_KNIFE = {}, {}
for k in pairs(CANDIDATE_KNIFE) do HEAD_KNIFE[k] = true; TAIL_KNIFE[k] = true end
for k in pairs(HEAD_KNIFE_EXTRA) do HEAD_KNIFE[k] = true end
for k in pairs(TAIL_KNIFE_EXTRA) do TAIL_KNIFE[k] = true end

-- preFix18：阿拉伯/通用称谓三表（实机开罗三部曲教训）——
-- ①TITLES_GLUE 称谓粘连词：候选首段含这些二字词 = 人名与称谓/场所粘连
--   （"炒货店老板艾布·赛利阿""新郎赫利勒·肖克特""乌姆·赫奈斐"类），
--   自动建组对整条候选跳过（宁漏勿错：乌姆·赫奈斐这类真人名由 AI 归组兜住）。
-- ②HONORIFIC_NICKS 纯尊称词：单用不得当昵称（实机"艾米娜→乌姆"毒——
--   乌姆/艾布是"某人之母/父"尊称，阿卜杜单用不是人名，②③档候选命中即跳）。
-- ③TITLES_TAIL 称谓尾词：叫法以这些词收尾 = 扫描粘连/尊称连写
--   （"阿卜杜胡咖啡馆""宰格鲁勒帕夏""穆泰瓦里谢赫"类），AI 组成员剔除+
--   提名拒收。刻意不收 神父/长老/上校/先生——俄苏书里"佐西马长老""X神父"
--   是实证合法通称（r8 提名 62 次放行），不能一刀切。
local TITLES_GLUE = {
  ["先生"]=true,["太太"]=true,["夫人"]=true,["小姐"]=true,["大叔"]=true,
  ["大婶"]=true,["少爷"]=true,["老板"]=true,["老板娘"]=true,["新郎"]=true,
  ["神父"]=true,["长老"]=true,["上校"]=true,["中校"]=true,["少校"]=true,
  ["上尉"]=true,["中尉"]=true,["少尉"]=true,["将军"]=true,["大夫"]=true,
  ["医生"]=true,["护士"]=true,["谢赫"]=true,["帕夏"]=true,["贝伊"]=true,
  ["贝克"]=true,["乌姆"]=true,["艾布"]=true,["阿布"]=true,["阿卜杜"]=true,
  ["咖啡馆"]=true,["酒吧"]=true,["旅馆"]=true,["饭店"]=true,["客栈"]=true,
  ["茶馆"]=true,["修士"]=true,["修女"]=true,["嬷嬷"]=true,["管家"]=true,
  ["门房"]=true,["仆人"]=true,["侍者"]=true,["女仆"]=true,
}
local HONORIFIC_NICKS = {
  ["乌姆"]=true,["艾布"]=true,["阿布"]=true,["阿卜杜"]=true,["谢赫"]=true,
  ["帕夏"]=true,["贝伊"]=true,["贝克"]=true,["西迪"]=true,["哈吉"]=true,
}
local TITLES_TAIL = {
  ["咖啡馆"]=true,["酒吧"]=true,["旅馆"]=true,["饭店"]=true,["客栈"]=true,
  ["茶馆"]=true,["谢赫"]=true,["帕夏"]=true,["贝伊"]=true,["贝克"]=true,
}
local function firstTitleGlue(s)
  for w in pairs(TITLES_GLUE) do
    if s:find(w, 1, true) then return w end
  end
  return nil
end
local function tailTitleGlue(s)
  for w in pairs(TITLES_TAIL) do
    if #s > #w and s:sub(-#w) == w then return w end
  end
  return nil
end
local function isHonorificNick(w)
  return HONORIFIC_NICKS[w] == true
end
-- preFix18：阿拉伯文学特征触发（prompt 领域提示注入用）——候选中含阿拉伯
-- 专有标记词的达到阈值即判 ar；其余语种不注入（现 prompt 即俄苏调校）。
local ARAB_MARKS = {
  ["乌姆"]=true,["艾布"]=true,["阿布"]=true,["阿卜杜"]=true,["谢赫"]=true,
  ["帕夏"]=true,["贝伊"]=true,["贝克"]=true,["西迪"]=true,["哈吉"]=true,
}
local function detectArabicCandidates(candidates)
  local n = 0
  for _, w in ipairs(candidates or {}) do
    for mark in pairs(ARAB_MARKS) do
      if w:find(mark, 1, true) then n = n + 1 break end
    end
  end
  return n >= 3
end

-- 取 UTF-8 串的首/末单字（字节截取，兼容 1~4 字节与 ·(2字节)）
local function utf8_head_tail(w)
  local n = #w
  if n == 0 then return "", "" end
  local b1 = w:byte(1)
  local hlen = (b1 >= 0xF0 and 4) or (b1 >= 0xE0 and 3) or (b1 >= 0xC0 and 2) or 1
  if hlen > n then hlen = n end
  local blen = 1
  while blen < n do
    local b = w:byte(n - blen + 1)
    if b >= 0xC0 then break end
    blen = blen + 1
  end
  return w:sub(1, hlen), w:sub(n - blen + 1)
end

-- 称谓前缀粘连检查：候选串以任一停用词（父亲/老头儿/未婚妻…）开头
-- 说明是"称谓+人名"粘连串（"父亲费奥多尔·巴甫洛维奇"），拒收。
-- "老卡拉马佐夫"不受影响——"老"本身不是停用词（"老头儿"才是）。
local function startsWithStopword(s)
  for w in pairs(CANDIDATE_STOPWORDS) do
    if s:sub(1, #w) == w then return true end
  end
  return false
end

-- 亲属序称残尾（v2.7.5 方案 B）：流式切刀"长"拆"长子德米特里"类亲属序称
-- 短语后，残尾以"子"字打头。中文 4+ 字人名首字"子"实际不存在（"子规"2 字、
-- 日名"…子"在尾），而残尾必然 ≥4 字（"子德米特里"5 字、提名裸串书里真实
-- 5 次，计数验证拦不住）。对 4~5 字扫描候选与 AI 提名统一拒收；
-- ≥6 字档已由首刀表["子"]全覆盖，此函数只兜 4~5 字。
local function isKinResidueHead(s)
  if type(s) ~= "string" then return false end
  return utf8len(s) >= 4 and s:sub(1, 3) == "子"
end

-- 「·德X」残尾（2026-09-28 百年孤独实机）：流式切刀从"费尔南达·德尔·卡皮奥"
-- "桑塔索菲亚·德拉·彼达"切出的中段残尾以「·德尔/·德拉」结尾——中文人名
-- 以「·德X」收尾的合法形态不存在（"德尔/德拉"是西语连接词 de la/de 的音译段，
-- 只能出现在名串中间）。≥6 字档扫描候选与 AI 提名统一拒收；「·」孤尾同洗
-- （"费尔南达·"类切刀断尾）。单字尾刀不能加"尔"——费奥多尔/彼乔林类真名
-- 以"尔"收尾会误杀，故用三字节模式匹配而非入 TAIL_KNIFE。
local function isDotResidueTail(s)
  if type(s) ~= "string" then return false end
  if s:match("·德[尔拉]$") then return true end
  local _, t = utf8_head_tail(s)
  return t == "·"
end

-- 简繁昵称偏好（2026-09-28 百年孤独实机，方案 A②）：同一人物的多个叫法被
-- AI 收进同组时可能简繁混排（奥雷里亚诺/奧雷里亚诺），③档按字节数排序繁简
-- 同长不分先后，曾选出繁体昵称「奧雷里亚诺」。此处只放繁→简映射（译名常见
-- 字），供自动昵称候选做让位判断。安全门：只在转换结果逐字等于组内已有叫法
-- 时才生效——映射表缺字最多不转换，任何误差都不会产生组外新串；全书只有
-- 繁体写法时没有简体孪生，昵称照旧，传统排版书不受影响。
local TRAD2SIMP = {
  ["奧"]="奥",["亞"]="亚",["爾"]="尔",["維"]="维",["納"]="纳",["達"]="达",
  ["諾"]="诺",["麗"]="丽",["華"]="华",["烏"]="乌",["蘇"]="苏",["葉"]="叶",
  ["傑"]="杰",["倫"]="伦",["蘭"]="兰",["凱"]="凯",["瓊"]="琼",["錢"]="钱",
  ["鍾"]="钟",["麥"]="麦",["遜"]="逊",["賽"]="赛",["繆"]="缪",["賓"]="宾",
  ["費"]="费",["揚"]="扬",["薩"]="萨",["瑪"]="玛",["貝"]="贝",["喬"]="乔",
  ["萬"]="万",["愛"]="爱",["絲"]="丝",["車"]="车",["東"]="东",["樂"]="乐",
  ["盧"]="卢",["衛"]="卫",["廣"]="广",["張"]="张",["懷"]="怀",["驚"]="惊",
  ["猶"]="犹",["環"]="环",["發"]="发",["庫"]="库",["茲"]="兹",["頓"]="顿",
  ["濟"]="济",["歐"]="欧",["湯"]="汤",["畢"]="毕",["韋"]="韦",["紐"]="纽",
  ["婭"]="娅",["來"]="来",["謝"]="谢",["蓋"]="盖",["漢"]="汉",["馬"]="马",
  ["齊"]="齐",["萊"]="莱",["裡"]="里",["裏"]="里",["聖"]="圣",["堯"]="尧",
  ["羅"]="罗",["遼"]="辽",["約"]="约",["魯"]="鲁",["長"]="长",
}
local function toSimpName(s)
  if type(s) ~= "string" or s == "" then return s end
  local out = s:gsub("[\194-\233][\128-\191]+", TRAD2SIMP)
  return out
end

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
  -- preFix26：扫描文本源一律取「未替换原书」——组人需要的是真原文。
  -- 读替换版的后果（09-29 r26 实机实测）：①真名被自己的替换结果吃掉——安娜里
  -- 完整真名候选少 18 条（如「亚历山大·渥伦斯基」）；②替换后文本被切刀切出
  -- 动词/虚字残尾伪候选（「亚历山德罗维奇叹」「亚历山德罗维奇并」
  -- 「亚历山德罗维奇皱起眉头」）。同一套扫描器：设备在"先重置再扫"下得到
  -- 240 条候选 == 原书复刻 240 条（交集 100%），与替换版复刻仅 76.7% 重合。
  -- 故此处与 getBookFullText 同策略：有备份读备份，无备份（从未应用过）
  -- 自动退回书文件本身，行为与旧版一致。
  do
    local bp = getBackupPath(file)
    if lfs.attributes(bp) then file = bp end
  end
  local scan_cache_dir = cache_dir .. "/names_scan"
  pcall(function() ensureDir(scan_cache_dir) end)
  local cache_file = nil
  if file then
    local attr = lfs.attributes(file)
    if attr then
      -- |scan3：扫描器算法版本——v2.7.5 引入虚字切刀与长词补充后必须作废旧缓存；
      -- scan9（2026-09-27）：首刀"子"＋4~5 字档残尾守卫，作废含"子德米特里·
      -- 费奥多罗维奇"类残尾的旧缓存清单；
      -- scan10（2026-09-29）：preFix26 文本源改为未替换原书备份，语义变了，
      -- 作废全部旧清单（缓存键含路径，本已能分流，bump 是为语义留痕）
      cache_file = scan_cache_dir .. "/" .. md5(file .. "|" .. tostring(attr.size or 0) .. "|" .. tostring(attr.modification or 0) .. "|scan10"):sub(1, 16) .. ".json"
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
  logger.info("KOAI NameReplace: scan html_files=", #html_files, " chars=", #full,
    " src=", (file == doc.file and "book" or "original_backup"))

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
      -- scan8 二元泛词切刀：先试 2 汉字整词（如果/结果/如此/如何…），
      -- 命中整词切——泛词高频字（果/如）与人名用字的冲突在双字层终结
      local cut = false
      local b4 = full:byte(i + 3)
      if isLead(b4) then
        local b5, b6 = full:byte(i + 4), full:byte(i + 5)
        if b5 and b5 >= 0x80 and b5 <= 0xBF and b6 and b6 >= 0x80 and b6 <= 0xBF then
          local two = full:sub(i, i + 5)
          if BIGRAM_KNIFE[two] then
            flush()
            i = i + 6
            cut = true
          end
        end
      end
      if not cut then
      local ch = full:sub(i, i + 2)
      if CANDIDATE_KNIFE[ch] then
        -- v2.7.5 虚字切刀：当前词在此断开（刀字自身不入频，单字过不了 ≥2 过滤）。
        -- "在佐西马长老的灵柩旁" → 在|佐西马长老|的|灵柩旁，藏串人名得以独立成词
        flush()
        i = i + 3
      elseif cur and i == cur_e + 1 then
        -- 相邻汉字：拼进当前词
        cur, cur_e = cur .. ch, i + 2
        i = i + 3
      else
        flush()
        cur, cur_e = ch, i + 2
        i = i + 3
      end
      end
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
  -- v2.7.5 双通道入选（译本无关，纯本地统计）：
  -- ①频次 top-160：短词多噪声，阈值高（卡拉马佐夫实测边界 count≈40）；
  -- ②长词补充：4 字以上且 ≥12 次者无视 top160 直接入选——中文里 4 字以上
  --   连续共现是强人名信号（佐西马长老/费奥多尔·巴甫洛维奇/伊波里特·基里洛维奇），
  --   按频次排序常被高频对话词挤出前 160。总上限 240 条（约 0.5K token）。
  local picked = {}
  local n_top = math.min(#candidates, 160)
  for i = 1, n_top do picked[#picked + 1] = candidates[i] end
  -- 长词通道按长度分级（v2.7.5 实机教训：全名"费奥多尔·巴甫洛维奇·卡拉马佐夫"
  -- 11 次、通称"老卡拉马佐夫"10 次，都差 1 次够不着 12 次门槛；而 AI 提名通道
  -- 两轮实测一次都没用——指望 AI 自觉不靠谱，超长串本地确定性收录）：
  --   ≥8 字 且 ≥2 次（超长串避开全部刀字几乎必然是人名全名/固定称谓）
  --   6~7 字 且 ≥8 次
  --   4~5 字 且 ≥12 次（原门槛）
  local washed_cnt = 0
  for i = n_top + 1, #candidates do
    local c = candidates[i]
    local L = utf8len(c.name)
    -- 6~7 字档门槛 8→6（2026-09-27 复算教训："老卡拉马佐夫"token 频次 6——
    -- plain 10 次中 4 处前字非刀被粘连成更长串；有首尾洗刀兜底，放低不脏）
    if (L >= 8 and c.count >= 2) or (L >= 6 and c.count >= 6) or (L >= 4 and c.count >= 12) then
      -- 首尾洗刀+称谓前缀粘连只作用于 ≥6 字新档两档；4~5 字老档与 top160 不洗防回归
      local washed = false
      if L >= 6 then
        local h, t = utf8_head_tail(c.name)
        if HEAD_KNIFE[h] or TAIL_KNIFE[t] or startsWithStopword(c.name) or isDotResidueTail(c.name) then washed = true end
      elseif isKinResidueHead(c.name) then
        -- 4~5 字档仅拦"子"头残尾（≥6 字档已由首刀表全覆盖）；其余照旧不洗防误杀
        washed = true
      end
      if washed then
        washed_cnt = washed_cnt + 1
      else
        picked[#picked + 1] = c
      end
    end
  end
  if washed_cnt > 0 then
    logger.info("KOAI NameReplace: 长词首尾洗刀剔除 =", washed_cnt)
  end
  while #picked > 240 do table.remove(picked) end
  local out = {}
  for _, c in ipairs(picked) do out[#out + 1] = c.name end

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

-- v2.7.5（三）：AI 提名稀有叫法的本地硬验证——解包全书逐字计数。
-- 扫描清单只收高频词，"老卡拉马佐夫"这类出现十次上下的稀有叫法进不了
-- 候选清单，改由 AI 按文学知识提名、此处逐字验证兜底：出现 ≥2 次才放行，
-- 凭空捏造的写法（无论多像通行译名）一律挡在门外。验证与扫描同源
-- （解包 → 剥标签 → 字节级 plain find），一次解包批量验证全部提名词。
-- 全书纯文本提取（会话内缓存）：解包 → 剥标签 → 拼接。缓存键 = 文件|size|mtime，
-- 应用替换写回后书文件变化自动失效。归组流程三处计数共用（关联叫法展开/提名
-- 验证/昵称撞形提示），PW4 上解包一次约 2 秒，必须避免重复解包。
local _fulltext_key, _fulltext = nil, nil
-- preFix24：改 `local function` 为函数定义——截断闸（truncationSuspect）与
-- sanitizePoisonRules 都在此定义点之前，需靠 716 行的前向声明拿到同一个局部。
function getBookFullText(original_file)
  if not original_file or not isEpub(original_file) then return nil end
  -- preFix25：全文文本一律取「未替换原书」——本函数是唯一入口，在这里收敛。
  -- 根因（09-29 实机）：重建式应用（v2.7.5）把原文备份在 koai_name_cache/originals/，
  -- 而"书路径"在应用过后就是替换版；getOriginalFile 依赖的 *.original_path 标记
  -- 全代码只有"读"(L135)与"删"(L272)、从无"写"，所以它永远退化成书路径本身。
  -- 于是所有"数原文"的判据读到的都是自己的替换结果，证据被自己擦掉：
  --   SC 查尔斯·达 56 次 / BN 庇拉尔·特尔 56 次 / AK 谢尔盖·伊万 291 次
  --   在原书里命中，在替换版里全是 0 次 → 截断闸/复姓连写闸双双静默失效、
  --   应用前自愈一条都拦不下（只有"瓦西里"那种残留形被歪打正着拦到）。
  -- 判据共用本函数（自愈、复姓连写、截断、提名验证、关联叫法展开），故在入口
  -- 收敛一次即可，胜过逐个调用点打补丁；未应用过的书无备份，自动退回书文件本身。
  do
    local bp = getBackupPath(original_file)
    if lfs.attributes(bp) then original_file = bp end
  end
  local attr = lfs.attributes(original_file)
  local key = original_file .. "|" .. tostring(attr and attr.size or 0)
      .. "|" .. tostring(attr and attr.modification or 0)
  if _fulltext_key == key and _fulltext then return _fulltext end
  local temp_dir = extractEpub(original_file)
  if not temp_dir then return nil end
  local html_files = {}
  local function collect(dir)
    for entry in lfs.dir(dir) do
      if entry ~= "." and entry ~= ".." then
        local path = dir .. "/" .. entry
        local attr2 = lfs.attributes(path)
        if attr2 then
          if attr2.mode == "directory" then
            collect(path)
          elseif attr2.mode == "file" and (path:match("%.x?html$") or path:match("%.xhtml$")) then
            html_files[#html_files + 1] = path
          end
        end
      end
    end
  end
  collect(temp_dir)
  table.sort(html_files)
  local all_text = {}
  for _, path in ipairs(html_files) do
    local ok, text = pcall(function()
      local f = io.open(path, "r")
      if not f then return nil end
      local html = f:read("*all")
      f:close()
      return htmlToText(html)
    end)
    if ok and type(text) == "string" then all_text[#all_text + 1] = text end
  end
  cleanupTempDir(temp_dir)
  _fulltext_key = key
  _fulltext = table.concat(all_text, "\n")
  return _fulltext
end

local countWordOccurrences
function countWordOccurrences(original_file, words)
  local counts = {}
  if #words == 0 then return counts end
  local full = getBookFullText(original_file)
  if not full then return counts end
  for _, w in ipairs(words) do
    local c, pos = 0, 1
    while true do
      local s = full:find(w, pos, true)
      if not s then break end
      c = c + 1
      pos = s + #w
    end
    counts[w] = c
  end
  return counts
end

-- preFix24：真名截断闸判据（方案 B）。返回 c（判为"更长固定串的碎片"）或 nil。
-- 判据见 716 行附近的 TRUNC_TAIL_EXCLUDE 注释；两处调用：
--   ① saveGroups 建规则前拒建（只拦不并，真名保持原文）
--   ② sanitizePoisonRules 应用前自愈停用存量毒规则（正文由重建式应用自动还原）
-- 性能：每条规则两次全文 plain find（命中点遍历 + 延长形计数），全文走
-- getBookFullText 会话缓存，一本书只解包一次；规则数 ≤ 数十条，开销可控。
function truncationSuspect(original_file, name)
  if type(name) ~= "string" or name == "" then return nil end
  local full = getBookFullText(original_file)
  if not full then return nil end
  local len = #name
  local cnt, han_total = 0, 0
  local nxt = {}
  local pos = 1
  while true do
    local s = full:find(name, pos, true)
    if not s then break end
    cnt = cnt + 1
    local e = s + len
    local b = full:byte(e)
    if b and b >= 0xE4 and b <= 0xE9 then
      local nch = full:sub(e, e + 2)
      nxt[nch] = (nxt[nch] or 0) + 1
      han_total = han_total + 1
    end
    pos = s + len
  end
  if cnt < 3 or han_total == 0 then return nil end
  local top, topn = nil, 0
  for k, v in pairs(nxt) do
    if v > topn then top, topn = k, v end
  end
  if not top then return nil end
  if topn * 10 < han_total * 7 then return nil end   -- 集中度 < 70%
  if TRUNC_TAIL_EXCLUDE[top] then return nil end
  local longer, elen, ext, p2 = name .. top, len + #top, 0, 1
  while true do
    local s = full:find(longer, p2, true)
    if not s then break end
    ext = ext + 1
    p2 = s + elen
  end
  if ext < 3 then return nil end
  return top, topn, han_total, cnt, ext
end

-- preFix30（块 B4）：昵称半截判据——"候选末尾字其实是头衔的首字"。
-- 为什么不能用上一套（truncationSuspect 的 TRUNC_TAIL_EXCLUDE 或"从不单独出现"
-- 这类泛判据）：
--   ① TRUNC_TAIL_EXCLUDE 为防"原名"误判收了 长/先/父/神 等称谓首字，可"昵称是
--      半截名"恰恰表现为后接这些字（巴利探长→巴利探），复用会被排除表挡掉。
--   ② "从不单独出现"太宽：中文译本里"特奥菲洛·巴尔加斯将军"这类**总带军衔**
--      的真姓氏（巴尔加斯，BN 实测）会被误判成碎片，反而把好昵称降级。
-- 现判据只认一种铁证形态：候选的**末字**与原文紧跟在它后面的字，恰好拼出一个
-- 头衔/身份词的**前两字**——说明这个末字真正属于头衔，是被洗刀从"名+头衔"上
-- 切下来时误并进候选的：
--     候选 = 穆赫辛·阿卜杜勒·巴**利探**，原文紧跟「长」→ 探+长 = 探长 ✓ 半截
--     候选 = 特奥菲洛·巴尔加斯，原文紧跟「将」→ 斯+将 ≠ 任何头衔 → 放行 ✓
-- 判据要 候选出现 ≥2 次 且 至少一次命中上表。命中只降档改选别的叫法，
-- 绝不改正文（宁漏勿错）。
-- 实机病例：NGF/MQ 纳吉布「巴利探」（原书 2 次全是"巴利探长"）被当昵称，
-- 裸「穆赫辛」16 处全变成「巴利探」→ 正文出现「巴利探简直不敢相信」。
local TITLE_BIGRAMS = {
  ["探长"] = true, ["将军"] = true, ["先生"] = true, ["小姐"] = true,
  ["夫人"] = true, ["太太"] = true, ["教授"] = true, ["大夫"] = true,
  ["医生"] = true, ["护士"] = true, ["博士"] = true, ["上校"] = true,
  ["中校"] = true, ["少校"] = true, ["上尉"] = true, ["中尉"] = true,
  ["少尉"] = true, ["准尉"] = true, ["队长"] = true, ["船长"] = true,
  ["站长"] = true, ["老板"] = true, ["主编"] = true, ["主席"] = true,
  ["总理"] = true, ["大臣"] = true, ["法官"] = true, ["律师"] = true,
  ["修士"] = true, ["修女"] = true, ["总管"] = true, ["管家"] = true,
  ["亲王"] = true, ["公爵"] = true, ["伯爵"] = true, ["男爵"] = true,
  ["子爵"] = true, ["侯爵"] = true, ["陛下"] = true, ["殿下"] = true,
  ["校长"] = true, ["院长"] = true,
}
local function nickFragmentSuspect(original_file, nick)
  if type(nick) ~= "string" or #nick < 6 then return nil end
  local last = nick:sub(-3)
  local b0 = last:byte(1)
  if not b0 or b0 < 0xE4 or b0 > 0xE9 then return nil end
  local full = getBookFullText(original_file)
  if not full then return nil end
  local len = #nick
  local cnt, hit = 0, nil
  local pos = 1
  while true do
    local s = full:find(nick, pos, true)
    if not s then break end
    cnt = cnt + 1
    local e = s + len
    local b1 = full:byte(e)
    if b1 and b1 >= 0xE4 and b1 <= 0xE9 then
      local big = last .. full:sub(e, e + 2)
      if TITLE_BIGRAMS[big] then hit = hit or big end
    end
    pos = s + len
  end
  if cnt < 2 then return nil end
  return hit
end

-- 纯父称判定（v2.7.5）：不含·且以父称后缀结尾（帕尔菲诺维奇/伊里奇/伊万诺夫娜…）。
-- 名+父称（含·）不算——2026-09-27 修正 16 词误杀 320 次的教训。
-- 提为文件级：父称防线与关联叫法展开两处共用。
local function isPatronymic(w)
  if w:find("·", 1, true) then return false end
  return utf8len(w) >= 3 and (w:match("维奇$") or w:match("夫娜$")
    or w:match("芙娜$") or w:match("耶芙娜$") or w:match("叶芙娜$")
    or w:match("伊里奇$"))
end

-- preFix30（块 D 辅助）：父称形态·宽松版——只用于"父称组"识别（见越界过滤）。
-- 比 isPatronymic 多认 "…奇$"（俄译名以奇收尾的父称极多：费奥多雷奇/库兹米奇/
-- 马夫里基奇/马卡雷奇/博里塞奇，旧表只列了 维奇/伊里奇 故漏）。误判面用
-- "整组成员级"判据兜住：只有当一个组**除了父称就是含该父称的全名**时才丢，
-- 故偶发误判的角色组（组里另有独立叫法）不会被牵连。误判代价=该组不建（宁漏）。
local function isPatronymicLoose(w)
  if type(w) ~= "string" or w:find("·", 1, true) then return false end
  if utf8len(w) < 3 then return false end
  return w:match("奇$") ~= nil or w:match("夫娜$") ~= nil
      or w:match("芙娜$") ~= nil or w:match("叶芙娜$") ~= nil
end

-- preFix30（块 B5）：称谓/职业尾剥离（剥，不是丢）。
-- 实机 r30 用户报：NGF/MQ 纳吉布「阿拉丁·卡希里教授 → 卡希里教授」
-- 「阿卜杜·迈瓦希卜大叔 → 迈瓦希卜大叔」——职业词被粘进昵称。
-- 与块 B3（类别尾）的区别：B3 是"支系/爵士"这类**类别**，整条叫法不是具体人，
-- 直接剔；B5 是"X教授/X大叔"这类**人称+身份**，人是对的，只是昵称多了个尾巴，
-- 故只把尾巴剥掉当**昵称候选**（original 不动，替换方向不变）。
-- 收词克制：刻意不收 先生/夫人/太太/小姐/长老/神父/上校/将军——俄苏书里
-- "佐西马长老""帕伊西神父""马德兰先生"是实证合法通称（KM/LS 现存规则就在用），
-- 收了等于拆东墙补西墙。只收"职业/泛称"里确定不该当昵称尾巴的 9 个。
local TITLE_STRIP = {
  ["教授"] = true, ["大叔"] = true, ["大婶"] = true, ["大夫"] = true,
  ["医生"] = true, ["护士"] = true, ["老师"] = true, ["老板"] = true,
  ["老板娘"] = true,
}
-- 剥尾：s 以 TITLE_STRIP 词收尾且剥后仍是 ≥2 汉字 → 返回短形，否则 nil。
local function stripTitleTail(s)
  if type(s) ~= "string" then return nil end
  for w in pairs(TITLE_STRIP) do
    if #s > #w and s:sub(-#w) == w then
      local head = s:sub(1, #s - #w)
      if utf8len(head) >= 2 then return head end
    end
  end
  return nil
end

-- preFix32（2026-09-29）：短语/称谓守卫——WPa《战争与和平》实锤三毒。
-- ①短语残渣当叫法：「皮埃尔觉得→皮埃尔」「到皮埃尔→皮埃尔」——扫描候选把
--   介词/副词开头的短语、动词收尾的短语当成了人名，AI 照单全收；建规则替换后
--   正文直接咬碎（「走到皮埃尔面前」→「走皮埃尔面前」）。
-- ②爵位被整词剥掉：「安德烈公爵→安德烈」「亚历山大皇帝→亚历山大」「玛丽亚
--   公爵小姐→玛丽亚」「罗斯托夫家→罗斯托夫」——preFix30 prompt 第 11 条教 AI
--   "剥身份词"，在俄译书上把爵位尊称剥没了（正文整词丢失）。爵位/尊称是人物
--   通行叫法的一部分：原名带称谓而昵称不带 → 拒建该条，称谓保持原文。
-- ③裸父称改本人名：「安德烈伊奇→安德烈」——光杆父称是行文称谓（仆称/尊称），
--   改成本人名会改变语体，拒建宁漏勿错。
-- 三个判据全部纯字符串，进建规则闸与应用前自愈（sanitizePoisonRules）两处。
local NOBLE_KEEP_TAILS = {
  ["公爵"] = true, ["伯爵"] = true, ["男爵"] = true, ["子爵"] = true,
  ["侯爵"] = true, ["亲王"] = true, ["王子"] = true, ["公主"] = true,
  ["皇帝"] = true, ["皇后"] = true, ["国王"] = true, ["女王"] = true,
  ["王后"] = true, ["沙皇"] = true, ["大公"] = true, ["老爷"] = true,
  ["大人"] = true, ["少爷"] = true, ["小姐"] = true, ["夫人"] = true,
  ["太太"] = true, ["先生"] = true, ["将军"] = true, ["上校"] = true,
  ["殿下"] = true, ["陛下"] = true, ["主教"] = true, ["神父"] = true,
  ["长老"] = true, ["家"] = true,
}
-- 虚词/介词开头（首个汉字）：译文人名几乎不可能以这些字开头。刻意不收
-- 老/小/大（老卡拉马佐夫/小约翰 是合法形态）；也不收 和/都/曾/正/将/会/能/要
-- （和田/正雄=日语名、曾=中文姓氏，误拦代价是少建规则虽无危害但白丢替换）。
local PHRASE_HEADS = {
  ["到"] = true, ["在"] = true, ["对"] = true, ["给"] = true, ["向"] = true,
  ["从"] = true, ["被"] = true, ["把"] = true, ["让"] = true, ["跟"] = true,
  ["朝"] = true, ["往"] = true, ["与"] = true, ["连"] = true, ["就"] = true,
  ["还"] = true, ["又"] = true, ["只"] = true, ["更"] = true, ["最"] = true,
  ["很"] = true, ["已"] = true, ["该"] = true, ["趁"] = true, ["替"] = true,
  ["比"] = true, ["照"] = true, ["按"] = true, ["据"] = true, ["凭"] = true,
  ["因"] = true, ["自"] = true,
}
-- 动词性双字收尾：人名不会以这些词结尾（觉得/知道…）。与
-- endsWithResidueVerb（单字：笑哭喊叫…）互补，那条管昵称残尾，这条管
-- 扫描候选整串。
local PHRASE_TAILS = {
  ["觉得"] = true, ["知道"] = true, ["认为"] = true, ["以为"] = true,
  ["希望"] = true, ["开始"] = true, ["继续"] = true, ["说道"] = true,
  ["回答"] = true, ["感到"] = true, ["显得"] = true, ["变成"] = true,
  ["成为"] = true, ["来到"] = true, ["说起"] = true, ["提到"] = true,
  ["谈到"] = true, ["走进"] = true, ["走出"] = true, ["回到"] = true,
  ["望着"] = true, ["望著"] = true, ["看见"] = true, ["听见"] = true,
}
-- s 以 NOBLE_KEEP_TAILS 词收尾 → 返回该称谓，否则 nil。
local function nobleTailOf(s)
  if type(s) ~= "string" then return nil end
  for w in pairs(NOBLE_KEEP_TAILS) do
    if #s > #w and s:sub(-#w) == w then return w end
  end
  return nil
end
-- preFix34（2026-09-29 晚）：统一身份词表。preFix32 只收 30 个爵位词，实机
-- 8 书再抓虫：爷爷/伯伯/公公/舅舅（亲属）、少校/医生/牧师/检察官（职业/军衔）、
-- 爵士/支系（类别）、本人/三号（杂类）全部漏网被砍；且「乐队指挥多皮阿·帕弗」
-- 「水手辛巴德」「居民斐理普·匹瑞普暨夫人乔治安娜」这类身份词开头的短语、
-- 「检察官→维尔福」「法里亚→教士」「埃弗瑞蒙德→侯爵」这类昵称本身是身份词的
-- 也全放行了。 doctrine 收紧为：**原名含身份词（头/尾/整词）→ 整条拒建（原文
-- 保持不动）；昵称本身是身份词 → 拒建**。唯一豁免：昵称保留同一个身份词
-- （德·维尔福夫人→维尔福夫人、米里哀先生→主教先生 同尾放行）。
-- preFix35（2026-09-29 深夜）：主动审计——列举式词表追不完，按「音译人名不以
-- 该词收尾/开头」的翻译惯例不变量一次收齐 尊称/王室/政军衔/警探/教会/仆役/
-- 手艺/贩夫/亲属三代的常见词；泛称批（姑娘/少年/男人…）并入尾表，补上守卫
-- ③此前查不到 GENERIC_TAILS 的缺口（昵称=「姑娘」这类整词泛称原本会漏网）。
-- 误拦代价=漏建规则宁漏勿错，绝不产生正文咬伤。
local IDENTITY_TAILS = {
  -- 爵位/王室/尊称（承 preFix32 NOBLE_KEEP_TAILS）
  ["公爵"] = true, ["伯爵"] = true, ["男爵"] = true, ["子爵"] = true,
  ["侯爵"] = true, ["亲王"] = true, ["王子"] = true, ["公主"] = true,
  ["皇帝"] = true, ["皇后"] = true, ["国王"] = true, ["女王"] = true,
  ["王后"] = true, ["沙皇"] = true, ["大公"] = true, ["老爷"] = true,
  ["大人"] = true, ["少爷"] = true, ["小姐"] = true, ["夫人"] = true,
  ["太太"] = true, ["先生"] = true, ["女士"] = true, ["将军"] = true,
  ["上校"] = true, ["殿下"] = true, ["陛下"] = true, ["主教"] = true,
  ["神父"] = true, ["长老"] = true, ["家"] = true,
  -- 爵位/类别
  ["爵士"] = true, ["支系"] = true, ["家族"] = true, ["氏族"] = true,
  -- 亲属
  ["爷爷"] = true, ["奶奶"] = true, ["外公"] = true, ["外婆"] = true,
  ["伯伯"] = true, ["叔叔"] = true, ["舅舅"] = true, ["姑姑"] = true,
  ["姑妈"] = true, ["姨妈"] = true, ["婶婶"] = true, ["公公"] = true,
  ["婆婆"] = true, ["岳父"] = true, ["岳母"] = true, ["大娘"] = true,
  ["大妈"] = true, ["大婶"] = true, ["大叔"] = true,
  -- 职业/军衔
  ["医生"] = true, ["大夫"] = true, ["护士"] = true, ["老师"] = true,
  ["教师"] = true, ["教授"] = true, ["博士"] = true, ["牧师"] = true,
  ["神甫"] = true, ["教士"] = true, ["检察官"] = true, ["法官"] = true,
  ["律师"] = true, ["船长"] = true, ["水手"] = true, ["管家"] = true,
  ["仆人"] = true, ["女仆"] = true, ["老板"] = true, ["少校"] = true,
  ["中将"] = true, ["少将"] = true, ["上将"] = true, ["上尉"] = true,
  ["中尉"] = true, ["少尉"] = true,
  -- 杂类/序号
  ["本人"] = true, ["一号"] = true, ["二号"] = true, ["三号"] = true,
  ["四号"] = true, ["五号"] = true,
  -- preFix35（2026-09-29 深夜）：主动审计补漏——词表是列举式，与其等下一本
  -- 书再被阁下/修女/嬷嬷/孙子/侄子/中校/骑士 打脸，不如按"音译人名不会以
  -- 这个词收尾"的不变量一次收齐常见类目。全部满足两条硬标准：
  --   a) 真音译名以它收尾 = 翻译惯例级不可能（误拦代价=漏建规则，宁漏勿错）；
  --   b) 它收尾的短语被建成规则 = 实机已验的毒形态（身份词被剥/整族改一人）。
  ["阁下"] = true, ["主人"] = true, ["领主"] = true,
  ["太子"] = true, ["王妃"] = true, ["太后"] = true, ["王储"] = true,
  ["首相"] = true, ["大臣"] = true, ["总统"] = true,
  ["元帅"] = true, ["中校"] = true, ["大尉"] = true,
  ["警长"] = true, ["探长"] = true, ["队长"] = true,
  ["修女"] = true, ["修士"] = true, ["嬷嬷"] = true,
  ["狱卒"] = true, ["邮差"] = true, ["仆役"] = true, ["侍从"] = true,
  ["随从"] = true, ["副官"] = true, ["秘书"] = true, ["学徒"] = true,
  ["伙计"] = true, ["店员"] = true, ["掌柜"] = true,
  ["奶妈"] = true, ["保姆"] = true, ["丫鬟"] = true, ["厨子"] = true,
  ["车夫"] = true, ["门房"] = true, ["房东"] = true, ["园丁"] = true,
  ["铁匠"] = true, ["木匠"] = true, ["裁缝"] = true, ["商人"] = true,
  ["店主"] = true, ["军官"] = true, ["士兵"] = true, ["哨兵"] = true,
  ["卫兵"] = true, ["骑兵"] = true, ["步兵"] = true, ["水兵"] = true,
  ["船员"] = true, ["飞行员"] = true,
  ["大伯"] = true, ["伯母"] = true, ["姑父"] = true, ["姨父"] = true,
  ["舅妈"] = true, ["嫂子"] = true, ["姐夫"] = true, ["妹夫"] = true,
  ["儿媳"] = true, ["女婿"] = true,
  ["侄子"] = true, ["侄女"] = true, ["侄儿"] = true, ["外甥"] = true,
  ["外甥女"] = true, ["孙子"] = true, ["孙女"] = true, ["外孙"] = true,
  ["继父"] = true, ["继母"] = true, ["养父"] = true, ["养母"] = true,
  ["继子"] = true, ["继女"] = true, ["养子"] = true, ["养女"] = true,
  ["义子"] = true, ["义女"] = true, ["私生子"] = true,
  ["干爹"] = true, ["干妈"] = true,
  ["表哥"] = true, ["表弟"] = true, ["表姐"] = true, ["表妹"] = true,
  ["堂哥"] = true, ["堂弟"] = true, ["堂姐"] = true, ["堂妹"] = true,
  ["大哥"] = true, ["大姐"] = true, ["兄弟"] = true,
  ["未婚夫"] = true, ["未婚妻"] = true, ["情妇"] = true, ["情夫"] = true,
  ["遗孀"] = true, ["寡妇"] = true, ["后裔"] = true, ["骑士"] = true,
  -- 泛称对齐（preFix23 GENERIC_TAILS 只进 strip/autoFill，守卫与自愈
  -- 此前查不到这批——昵称=「姑娘」这类整词泛称在守卫③是漏网的）
  ["老头"] = true, ["老太"] = true, ["老汉"] = true, ["老公"] = true,
  ["老婆"] = true, ["少年"] = true, ["少女"] = true, ["孩子"] = true,
  ["小孩"] = true, ["男人"] = true, ["女人"] = true, ["姑娘"] = true,
  ["小伙子"] = true,
  -- preFix37（2026-09-30 凌晨）：用户拍板「称谓一律保留原文，只统一名字」——
  -- 补齐词表审计缺口（对照爵位/宗教/军警/职衔/亲属/杂类六类清单逐词核查）。
  -- 全部满足两条硬标准：a) 音译人名以它收尾=翻译惯例级不可能；
  -- b) 它收尾的规则=称谓被削（佐西马长老→佐西马 类），按用户决策定性为毒。
  -- 爵位补充
  ["勋爵"] = true, ["王爷"] = true, ["爵爷"] = true,
  -- 宗教补充
  ["大主教"] = true, ["红衣主教"] = true, ["喇嘛"] = true, ["活佛"] = true,
  ["方丈"] = true, ["住持"] = true, ["和尚"] = true, ["道士"] = true,
  ["阿訇"] = true, ["拉比"] = true, ["司铎"] = true,
  -- 军警官补充
  ["军士"] = true, ["士官"] = true, ["警督"] = true, ["警官"] = true,
  ["司令"] = true, ["参谋长"] = true, ["大队长"] = true,
  -- 职业/职衔补充
  ["医师"] = true, ["管家婆"] = true, ["经理"] = true, ["大副"] = true,
  ["水手长"] = true, ["站长"] = true, ["行长"] = true, ["校长"] = true,
  ["院长"] = true, ["主任"] = true, ["科长"] = true, ["县长"] = true,
  ["市长"] = true, ["省长"] = true, ["总理"] = true, ["部长"] = true,
  ["局长"] = true, ["书记官"] = true, ["刽子手"] = true,
  -- 亲属称呼补充
  ["大爷"] = true, ["老爹"] = true, ["老妈"] = true, ["老爷子"] = true,
  ["老太太"] = true, ["小弟"] = true, ["小妹"] = true, ["哥哥"] = true,
  ["姐姐"] = true, ["弟弟"] = true, ["妹妹"] = true, ["大嫂"] = true,
  ["二嫂"] = true, ["少奶奶"] = true, ["姑爷"] = true,
  ["教父"] = true, ["教母"] = true,
  -- 杂类身份补充
  ["老太婆"] = true, ["徒弟"] = true, ["师傅"] = true, ["东家"] = true,
  ["客人"] = true, ["房客"] = true, ["佃户"] = true, ["农奴"] = true,
  ["奴隶"] = true, ["下人"] = true,
}
-- 身份词开头的短语（职业/亲属前缀＋人名）：替换必砍掉前缀 → 拒建。
local IDENTITY_HEADS = {
  ["乐队指挥"] = true, ["乐队"] = true, ["水手"] = true, ["水兵"] = true,
  ["居民"] = true, ["检察官"] = true, ["法官"] = true, ["律师"] = true,
  ["教授"] = true, ["老师"] = true, ["教师"] = true, ["医生"] = true,
  ["大夫"] = true, ["护士"] = true, ["牧师"] = true, ["神父"] = true,
  ["神甫"] = true, ["教士"] = true, ["主教"] = true, ["管家"] = true,
  -- preFix37：头位尊称（罗曼语系"红衣主教某某"式前序称谓）
  ["大主教"] = true, ["红衣主教"] = true,
  ["仆人"] = true, ["女仆"] = true, ["侍女"] = true, ["女佣"] = true,
  ["厨娘"] = true, ["厨师"] = true, ["车夫"] = true, ["马夫"] = true,
  ["门房"] = true, ["房东"] = true, ["园丁"] = true, ["铁匠"] = true,
  ["木匠"] = true, ["裁缝"] = true, ["商人"] = true, ["店主"] = true,
  ["船长"] = true, ["士兵"] = true, ["军官"] = true, ["哨兵"] = true,
  ["卫兵"] = true, ["爷爷"] = true, ["奶奶"] = true, ["外公"] = true,
  ["外婆"] = true, ["伯伯"] = true, ["叔叔"] = true, ["舅舅"] = true,
  ["姑姑"] = true, ["姨妈"] = true, ["婶婶"] = true, ["公公"] = true,
  ["婆婆"] = true,   ["少校"] = true, ["上校"] = true, ["中校"] = true,
  ["将军"] = true, ["上尉"] = true, ["中尉"] = true, ["少尉"] = true,
  ["老板"] = true,
  -- preFix35 头表补漏：与尾表同类目对齐（尾表拦「X修女」收尾，头表拦
  -- 「修女X」开头的短语，两向都得设防——preFix34 实锤「水手辛巴德」头形态）。
  ["修女"] = true, ["修士"] = true, ["嬷嬷"] = true,
  ["狱卒"] = true, ["邮差"] = true, ["仆役"] = true, ["侍从"] = true,
  ["随从"] = true, ["副官"] = true, ["秘书"] = true, ["学徒"] = true,
  ["伙计"] = true, ["店员"] = true, ["掌柜"] = true,
  ["奶妈"] = true, ["保姆"] = true, ["丫鬟"] = true, ["厨子"] = true,
  ["骑兵"] = true, ["步兵"] = true,
  ["元帅"] = true, ["大尉"] = true, ["警长"] = true, ["探长"] = true,
  ["队长"] = true, ["太子"] = true, ["王妃"] = true, ["太后"] = true,
  ["王储"] = true, ["首相"] = true, ["大臣"] = true, ["总统"] = true,
  ["领主"] = true, ["船员"] = true, ["飞行员"] = true,
  ["大伯"] = true, ["伯母"] = true, ["姑父"] = true, ["姨父"] = true,
  ["舅妈"] = true, ["嫂子"] = true, ["姐夫"] = true, ["妹夫"] = true,
  ["儿媳"] = true, ["女婿"] = true, ["侄子"] = true, ["侄女"] = true,
  ["外甥"] = true, ["孙子"] = true, ["孙女"] = true, ["外孙"] = true,
  ["继父"] = true, ["继母"] = true, ["养父"] = true, ["养母"] = true,
  ["表哥"] = true, ["表弟"] = true, ["表姐"] = true, ["表妹"] = true,
  ["堂哥"] = true, ["堂弟"] = true, ["堂姐"] = true, ["堂妹"] = true,
  ["老头"] = true, ["老汉"] = true, ["遗孀"] = true, ["寡妇"] = true,
  ["未婚妻"] = true, ["未婚夫"] = true,
}
-- w 本身（整词）是身份词 → true。
local function isPureIdentity(w)
  if type(w) ~= "string" then return false end
  return IDENTITY_TAILS[w] == true or IDENTITY_HEADS[w] == true
end
-- s 以身份词收尾 → 最长匹配的那个词，否则 nil。
local function identityTailOf(s)
  if type(s) ~= "string" then return nil end
  local best = nil
  for w in pairs(IDENTITY_TAILS) do
    if #s > #w and s:sub(-#w) == w then
      if not best or #w > #best then best = w end
    end
  end
  return best
end
-- s 以身份词开头（前缀）→ 最长匹配的那个词，否则 nil。
local function identityHeadOf(s)
  if type(s) ~= "string" then return nil end
  local best = nil
  for w in pairs(IDENTITY_HEADS) do
    if #s > #w and s:sub(1, #w) == w then
      if not best or #w > #best then best = w end
    end
  end
  return best
end
-- 短语残渣判定：虚词开头 / 动词双字收尾 / 不足两个汉字。
local function phraseSuspect(s)
  if type(s) ~= "string" or utf8len(s) < 2 then return true end
  local head = s:sub(1, 3)
  if PHRASE_HEADS[head] then return true end
  if utf8len(s) >= 3 and PHRASE_TAILS[s:sub(-6)] then return true end
  return false
end
-- 守卫（preFix34 四合一）：返回拒绝原因（字符串）或 nil。供 saveGroups 建规则
-- 链与 sanitizePoisonRules 自愈共用。
ruleGuardSuspect = function(n, target)
  if phraseSuspect(n) then return "短语残渣" end
  -- ⓪并列/杂糅短语（匹瑞普暨夫人乔治安娜）：中含「暨」必是多人并列，不是人名
  if type(n) == "string" and n:find("暨", 1, true) then return "并列短语" end
  -- ①原名以身份词收尾 → 只有昵称保留同一个词才放行（称谓必须原样保留）
  local it = identityTailOf(n)
  if it and not (type(target) == "string" and identityTailOf(target) == it) then
    return "身份尾削除（" .. it .. "）"
  end
  -- ②原名以身份词开头（乐队指挥X/水手X/居民X…）→ 昵称须保留同前缀
  local ih = identityHeadOf(n)
  if ih and not (type(target) == "string" and identityHeadOf(target) == ih) then
    return "身份头削除（" .. ih .. "）"
  end
  -- ③整词是身份词（检察官/侯爵/教士…）当原名或当昵称都拒
  if isPureIdentity(n) then return "纯身份词原名" end
  if type(target) == "string" and isPureIdentity(target) then
    return "昵称是身份词"
  end
  -- ④裸父称改本人名（preFix32 原判据保留）
  if isPatronymicLoose(n) and not isPatronymicLoose(target) then
    return "裸父称"
  end
  return nil
end

-- v2.7.5（五）B 方案：关联叫法展开——含·的全名机械拆出各段与逐级前缀组合。
-- 动机（阿黛拉伊达四轮实机教训）：一人多形态各自计数被稀释（裸名 token 11 次
-- 差 1 次够不着 4 字档 12 门槛），清单只见名+父称形态，AI 两轮归组均未主动
-- 提名裸名，形态集合永远凑不齐、组不成。拆段是机械操作无幻觉风险，plain≥2
-- 与提名验证同门槛；纯父称段与停用词一律排除。
local function expandRelatedNames(candidates, original_file)
  local have = {}
  for _, w in ipairs(candidates) do have[w] = true end
  local cand, seen = {}, {}
  for _, w in ipairs(candidates) do
    if w:find("·", 1, true) then
      -- 字节安全切法（与扫描侧 flush 同款）：先把 · 整体 gsub 成 \1 再按 [^\1]
      -- 切。不能直接 gmatch("[^·]+")——Lua 模式按字节工作，[^·] 会把 ·(C2 B7)
      -- 的两个字节都当分隔符，遇编码含 B7 的字（捷/德等）会拦腰截断（fengari
      -- harness 实测 卡捷琳娜→卡捷/琳娜、亚历山德罗维奇→亚历山德/罗维奇）。
      local segs = {}
      local tmp = w:gsub("·", "\1")
      for seg in tmp:gmatch("[^\1]+") do segs[#segs + 1] = seg end
      -- 2026-09-27 实机教训：书文本被坏规则污染后会出现
      -- "库兹马·萨姆索诺夫·库兹马·萨姆索诺夫"式重复串，拆出的段与组合
      -- 全是垃圾（碎片还会被 AI 归出跨人错组）——段有重复即整条跳过。
      local dup = false
      for i = 1, #segs do
        for j = i + 1, #segs do
          if segs[i] == segs[j] then dup = true break end
        end
        if dup then break end
      end
      if not dup then
        for _, s in ipairs(segs) do
          -- 段洗刀对齐扫描侧语义：仅 ≥6 字段做首尾检查（防"彼得/华生"类
          -- 短名误杀——"得/里"等人名风险字在尾刀表里）。06:06 实测脏书
          -- 拆出"伊万诺夫娜末"类碎片全靠 plain≥2 骗过门槛，源头补刀 +
          -- 重复段跳过 + 此处 ≥6 字洗刀三层布防。
          local h, tl = utf8_head_tail(s)
          if utf8len(s) >= 2 and not seen[s] and not have[s]
              and not CANDIDATE_STOPWORDS[s] and not isPatronymic(s)
              and not (utf8len(s) >= 6 and (HEAD_KNIFE[h] or TAIL_KNIFE[tl])) then
            seen[s] = true
            cand[#cand + 1] = s
          end
        end
        for i = 2, #segs - 1 do
          local combo = table.concat(segs, "·", 1, i)
          if not seen[combo] and not have[combo] then
            seen[combo] = true
            cand[#cand + 1] = combo
          end
        end
      end
    end
  end
  if #cand == 0 then return nil end
  local ok, counts = pcall(countWordOccurrences, original_file, cand)
  if not ok or not counts then return nil end
  local expanded = {}
  for _, w in ipairs(cand) do
    if (counts[w] or 0) >= 2 then expanded[#expanded + 1] = w end
  end
  if #expanded == 0 then return nil end
  table.sort(expanded)
  logger.info("KOAI NameReplace: 关联叫法展开 =", #expanded, "/", #cand,
    ":", table.concat(expanded, "/"))
  return expanded
end

-- ============ 硬证据否决层（v2.7.5 根治 AI 跨人错组，2026-09-27） ============
-- 背景（卡拉马佐夫全书审计）：AI 归组层在干净书上仍跨人错组 3 处
-- （帕伊西→佐西马、斯涅吉辽夫/尼古拉·伊里奇→伊柳沙、黎萨维塔·斯乜尔加夏娅
-- →莉兹）。同句共现"频次"已被数据证伪（合法对共现 7~17 句 > 错组对 2 句，
-- 叙述者同句内换称呼指同一人是常态），改用共现句"形态"做硬证据：
--   V1 亲属同位语：「A的儿子B」「A是B的儿子」——一个人不可能是自己的儿子；
--   V2 同名异父称：伊万·伊万诺维奇 vs 伊万·费奥多罗维奇——两代人；
--   V3 异称谓互动：同句「A神父…询问…B长老」——带两个不同称谓的互动句
--      只可能写两个人（帕伊西×佐西马两句实测全命中）。
-- 命中即整组否决：最坏后果 = 没合并（叫法保持原文），绝不是把 86 处
-- 帕伊西改成佐西马。全部字节级 plain find，与替换引擎同款无转义风险。

local VETO_KIN_WORDS = {
  "儿子", "女儿", "父亲", "母亲", "哥哥", "弟弟", "姐姐", "妹妹", "兄弟", "兄长",
  "爷爷", "奶奶", "外公", "外婆", "叔叔", "伯伯", "舅舅", "姑姑", "侄子", "外甥",
  "孙子", "孙女", "丈夫", "妻子", "长子", "次子", "三子", "幼子", "养子", "继子",
}

local VETO_TITLE_WORDS = {
  "长老", "神父", "神甫", "司祭", "辅祭", "修士", "修女", "主教", "大主教",
  "都主教", "将军", "上校", "上尉", "中尉", "少尉", "准尉", "医生", "大夫",
  "律师", "教授", "法官",
}

local VETO_TWO_PARTY_VERBS = {
  "询问", "求见", "拜见", "请教", "忏悔", "禀告", "吩咐", "嘱咐", "转告",
  "转达", "质问", "审问", "召见", "接见", "会见", "告诉",
}

local VETO_SENTENCE_ENDS = { "。", "！", "？", "\n" }

-- 字节安全切 ·（与 expandRelatedNames 同款：先 gsub 成 \1 再按 [^\1] 切，
-- 直接 gmatch("[^·]+") 会把编码含 B7 的字拦腰截断——harness 实测教训）
local function vetoSplitSegs(w)
  local tmp = w:gsub("·", "\1")
  local segs = {}
  for seg in tmp:gmatch("[^\1]+") do segs[#segs + 1] = seg end
  return segs
end

-- 名字后紧跟的称谓词（长老/神父/上尉…），无则 nil。
-- 嵌在更长人名内的出现自然跳过：后邻是「·」不可能匹配称谓。
local function vetoTitleAt(text, pos)
  for _, t in ipairs(VETO_TITLE_WORDS) do
    if text:sub(pos, pos + #t - 1) == t then return t end
  end
  return nil
end

-- 句界（字节安全）：对每个句末标点做 plain find 取最小；Lua 模式的
-- [。！？] 字符类按字节匹配会撞上汉字续字节，绝不能用。
local function vetoNextSentenceEnd(text, from)
  local best
  for _, p in ipairs(VETO_SENTENCE_ENDS) do
    local e = text:find(p, from, true)
    if e and (best == nil or e < best) then best = e end
  end
  return best
end

-- V1 亲属同位语：「A的<K>B」或「A是B的<K>」（K=亲属词，全部紧邻）。
-- 「斯涅吉辽夫的儿子伊柳沙」「伊柳沙是斯涅吉辽夫的儿子」两人铁证；
-- 叙述者同句换称呼指同一人不含亲属词（实测合法对 gap 全是 ·/——/同位语）。
--
-- 方案 A（2026-09-27 用户拍板，治首跑漏拦）：正文亲属同位写的是裸姓/裸名
-- （实书原句「退役上尉斯涅吉辽夫的儿子伊柳沙」），而 AI 组内往往只有全名
-- 「尼古拉·伊里奇·斯涅吉辽夫」——全名+的儿子全书 0 次，只拿原串查必漏。
-- 故把叫法按 · 拆出段变体交叉查找。段准入：≥2 汉字（防单字变体海量 find
-- 命中）且非纯父称（父称段语义弱、误杀面大；本案起作用的是姓段）。
local function vetoNameVariants(name)
  local variants = { name }
  if name:find("·", 1, true) then
    for _, seg in ipairs(vetoSplitSegs(name)) do
      if #seg >= 6 and not isPatronymic(seg) then
        variants[#variants + 1] = seg
      end
    end
  end
  return variants
end

-- preFix30：称谓插入词表——亲属同位句里夹在人物与其「的<K>」之间的身份词。
-- 用途见 vetoSkipInsert / vetoKinPairEvidence 注释。
local VETO_INSERT_TITLES = {
  "太太", "夫人", "小姐", "先生", "女士", "老太太", "老大娘", "大叔", "大婶",
  "大娘", "大妈", "少爷", "老爷", "妈妈", "爸爸", "母亲", "父亲",
}
-- 跳过（可选的）一个称谓插入词，返回跳过后的字节位置；没有则原样返回。
local function vetoSkipInsert(text, pos)
  for _, t in ipairs(VETO_INSERT_TITLES) do
    if text:sub(pos, pos + #t - 1) == t then return pos + #t end
  end
  return pos
end

local function vetoKinPairEvidence(full, a, b)
  local pos = 1
  while true do
    local p = full:find(a, pos, true)
    if not p then return false end
    local q = p + #a
    -- preFix30：允许 A/B 与「的<K>」之间夹一个称谓词（实书常写「莉兹是霍赫拉科娃
    -- 太太的女儿」；漏掉这层插入就漏掉"母亲被叫成女儿名"的铁证，KM 实机毒）。
    local q1 = vetoSkipInsert(full, q)
    local two = full:sub(q1, q1 + 2)
    if two == "的" then
      local base = q1 + 3
      for _, kin in ipairs(VETO_KIN_WORDS) do
        if full:sub(base, base + #kin - 1) == kin then
          local r = base + #kin
          if full:sub(r, r + #b - 1) == b then return true end
        end
      end
    elseif two == "是" then
      local base = q1 + 3
      if full:sub(base, base + #b - 1) == b then
        local r = vetoSkipInsert(full, base + #b)
        if full:sub(r, r + 2) == "的" then
          local base2 = r + 3
          for _, kin in ipairs(VETO_KIN_WORDS) do
            if full:sub(base2, base2 + #kin - 1) == kin then return true end
          end
        end
      end
    end
    pos = q
  end
end

local function vetoKinshipEvidence(full, a, b)
  for _, va in ipairs(vetoNameVariants(a)) do
    for _, vb in ipairs(vetoNameVariants(b)) do
      if vetoKinPairEvidence(full, va, vb) then return true end
    end
  end
  return false
end

-- V3 异称谓互动：同句内 A+称谓1 … [双方动词] … B+称谓2，两称谓不同。
-- 动词允许落在 B 之后（「佐西马长老素来向帕伊西神父进行忏悔」的忏悔在
-- B 后 4 字，gap 里的「向」是方向词不算动词）。
local function vetoTitleClashEvidence(full, a, b)
  local pos = 1
  while true do
    local p = full:find(a, pos, true)
    if not p then return false end
    local q = p + #a
    local ta = vetoTitleAt(full, q)
    if ta then
      local send = vetoNextSentenceEnd(full, q) or (q + 1200)
      local pb = full:find(b, q, true)
      if pb and pb < send then
        local qb = pb + #b
        local tb = vetoTitleAt(full, qb)
        if tb and tb ~= ta then
          local gap = full:sub(q + #ta, pb - 1)
          local after = full:sub(qb + #tb, qb + #tb + 23)
          local window = gap .. after
          for _, v in ipairs(VETO_TWO_PARTY_VERBS) do
            if window:find(v, 1, true) then return true end
          end
        end
      end
    end
    pos = q
  end
end

-- V2 同名异父称（纯结构，无需正文）：两叫法首段相同、第二段均为父称
-- 且不同 → 两代人（伊万·伊万诺维奇 vs 伊万·费奥多罗维奇）。
-- 父称宽类：第二段以「奇」收尾（维奇/伊里奇/马卡雷奇…）或「…夫娜/…奇娜」。
local function vetoPatronymicClash(a, b)
  local sa, sb = vetoSplitSegs(a), vetoSplitSegs(b)
  if #sa < 2 or #sb < 2 or sa[1] ~= sb[1] then return false end
  local p2a, p2b = sa[2], sb[2]
  if p2a == p2b then return false end
  local function patronymClass(s)
    if utf8len(s) < 3 then return nil end
    if s:match("奇$") then return "m" end
    if s:match("夫娜$") or s:match("芙娜$") or s:match("叶芙娜$")
        or s:match("耶芙娜$") or s:match("奇娜$") then return "f" end
    return nil
  end
  local ca, cb = patronymClass(p2a), patronymClass(p2b)
  return ca ~= nil and ca == cb
end

-- V4 前缀剥除（v2.7.5 治《百年孤独》美人儿蕾梅黛丝错组，2026-09-27 实锤）：
-- AI 把绰号/称号前缀从全名头部"剥"掉当昵称（美人儿+蕾梅黛丝→蕾梅黛丝），
-- 而裸名另有所指——范晔译本裸名"蕾梅黛丝"全书独立出现 58 次（另一人物，
-- 小蕾梅黛丝），美人儿全称 55 次，是两个活人撞形。纯形态判定无需正文。
-- 对组内有序对 (A,N)：N 为 A 的字节后缀且起点落在 UTF-8 字符边界 →
-- 前缀 P = A 去尾 N，四关全中才否决整组：
--   ① P ≥2 字符（单字前缀 老X/堂X/阿X 天然放行）；
--   ② P 非亲属序称（二哥伊万→伊万 剥的是修饰序称，保指称，豁免）；
--   ③ P 不以·结尾（音译名分隔 XX·YY→YY 放行）。
-- 两书 95 条已入库规则回归：卡拉马佐夫拦 0（二哥伊万获豁免），百年孤独
-- 精确拦 [18] 一条，误伤 0。与 V1-V3 同哲学：最坏后果 = 没合并。
local function utf8chars(s)
  local out = {}
  local i, n = 1, #s
  while i <= n do
    local c = s:byte(i)
    local len = 1
    if c >= 0xF0 then len = 4
    elseif c >= 0xE0 then len = 3
    elseif c >= 0xC0 then len = 2 end
    out[#out + 1] = s:sub(i, i + len - 1)
    i = i + len
  end
  return out
end

local VETO_KIN_PREFIX_CORE = {
  ["哥"]=true, ["弟"]=true, ["姐"]=true, ["妹"]=true, ["兄"]=true,
  ["叔"]=true, ["伯"]=true, ["舅"]=true, ["姑"]=true, ["姨"]=true, ["嫂"]=true,
}
local VETO_KIN_PREFIX_MOD = {
  ["大"]=true, ["小"]=true, ["二"]=true, ["三"]=true, ["四"]=true, ["五"]=true,
  ["六"]=true, ["七"]=true, ["八"]=true, ["九"]=true, ["十"]=true,
  ["第"]=true, ["老"]=true, ["幺"]=true, ["堂"]=true, ["表"]=true,
  ["亲"]=true, ["继"]=true, ["养"]=true, ["干"]=true, ["内"]=true,
}

-- 前缀是纯亲属序称：全部字符 ∈ 修饰∪核心，且至少一个核心字
-- （二哥/堂兄/老幺弟/小姨 通过；美人儿/俏姑娘/神父 不通过——"神"不在表）
local function vetoKinPrefix(prefix)
  local chars = utf8chars(prefix)
  if #chars == 0 then return false end
  local has_core = false
  for _, ch in ipairs(chars) do
    if VETO_KIN_PREFIX_CORE[ch] then
      has_core = true
    elseif not VETO_KIN_PREFIX_MOD[ch] then
      return false
    end
  end
  return has_core
end

local function vetoPrefixStrip(a, b)
  if type(a) ~= "string" or type(b) ~= "string" then return false end
  if a == b or #b == 0 or #a <= #b then return false end
  if a:sub(-#b) ~= b then return false end
  local start = #a - #b + 1
  if start > 1 then
    -- UTF-8 边界校验：起点字节不能是续字节（10xxxxxx），防字符腰斩假后缀
    local c = a:sub(start, start):byte()
    if c and c >= 0x80 and c < 0xC0 then return false end
  end
  local prefix = a:sub(1, start - 1)
  if utf8len(prefix) < 2 then return false end      -- ①单字前缀放行（老X/堂X/阿X）
  if vetoKinPrefix(prefix) then return false end    -- ②亲属序称豁免（二哥伊万→伊万）
  if prefix:sub(-#"·") == "·" then return false end -- ③音译分隔放行（XX·YY→YY）
  return true
end

-- V5 双父称冲突（v2.7.5 治卡拉马佐夫老卡组/卡嘉组错组，2026-09-27 实锤）：
-- AI 把家族父称张冠李戴当 canonical（老卡组 nick=费尧多罗维奇——老卡本人
-- 父称是巴甫洛维奇，费尧多罗维奇是他儿子们的父称），组内两叫法各含父称段
-- 且互非音译变体 → 组里混入了两代人/两个人，整组否决。V2 拦不住它：
-- V2 要求首段相同（费奥多尔≠费尧多罗维奇、卡捷琳娜≠叶卡杰丽娜首段异漏网）。
-- 变体判定：父称段同字数且逐字差 ≤1（费奥多罗维奇/费尧多罗维奇 音译差放行；
-- 男 -维奇 与女 -夫娜 收尾天然差 ≥2 字不会误放）。
-- 合法组放行边界：基里洛维奇/伊格纳启耶夫娜等"书内以父称通称"组内父称段
-- 相同或仅音译差；仅一方含父称段（库兹马·库兹米奇×库兹马·萨姆索诺夫）不
-- 触发；马卡雷奇/博里塞奇 不在 isPatronymic 收尾集，同组无父称段不触发。
-- 与 V1-V4 同哲学：最坏后果 = 没合并（整组放弃，交人工重新归组）。
local function vetoPatronymicSegs(s)
  local segs = {}
  local tmp = s:gsub("·", "\1")
  for seg in tmp:gmatch("[^\1]+") do
    if isPatronymic(seg) then segs[#segs + 1] = seg end
  end
  return segs
end

local function vetoPatronymicVariant(a, b)
  if a == b then return true end
  local ca, cb = utf8chars(a), utf8chars(b)
  if #ca ~= #cb then return false end
  local diff = 0
  for i = 1, #ca do
    if ca[i] ~= cb[i] then diff = diff + 1 end
  end
  return diff <= 1
end

local function vetoDualPatronymic(a, b)
  if type(a) ~= "string" or type(b) ~= "string" then return false end
  local sa, sb = vetoPatronymicSegs(a), vetoPatronymicSegs(b)
  if #sa == 0 or #sb == 0 then return false end
  for _, pa in ipairs(sa) do
    for _, pb in ipairs(sb) do
      if vetoPatronymicVariant(pa, pb) then return false end
    end
  end
  return true
end

-- preFix16（2026-09-29）：未覆盖·候选自动建组——AI 静默漏组的机械兜底。
-- 动机（阿黛拉伊达四轮实机教训）：阿黛拉伊达·伊万诺夫娜 19 处全文、扫描候选
-- 与展开段全齐，AI r7/r8 连续两轮拒建组——小模型不认识第一卷早逝配角，系统性
-- 而非采样方差。机械方案不依赖人工确认：扫描候选中含·且未被任何组/规则覆盖的
-- preFix22：译名残尾检定——音译人名段内不应出现叠字（哈哈/嘿嘿类拟声粘连：
-- Cairo 实机「艾哈迈德·阿卜杜·嘉瓦德哈哈大」=「…嘉瓦德」+「哈哈大笑」切刀残尾，
-- 建组后 2 处啃伤原文），段以高频动词收尾（大叫/笑道类粘连）同理。纯拒绝闸
-- （宁漏勿错）：只拦自动建组候选；四书现役规则反向验证零误杀。
-- preFix23 注：RESIDUE_TAIL_CHARS/endsWithResidueVerb 已上移至防串写区
-- （applyAndReload 自愈需要），此处仅保留 hasDoubledHan。
local function hasDoubledHan(s)
  for i = 1, #s - 5 do
    local b1 = s:byte(i)
    if b1 >= 0xE4 and b1 <= 0xE9 then
      if s:sub(i, i + 2) == s:sub(i + 3, i + 5) then return true end
    end
  end
  return false
end

-- 全名直接建组，昵称=末段（姓氏）优先/首段兜底（2-6 字），经 canonical 传入
-- saveGroups ②档必中，与 AI 组同走既有确认弹窗（同一清单多几行，无新增流程）。
-- 闸门（r8 两书 72 个·候选实测收敛：KM 建组 13 组全正、BN 0 组零破坏）：
--   ①父称收尾 ②停用词 ③存量昵称查重 ④包含消费（F⊃他组名→子串替换会先被
--   吃掉/咬名，死规则风险） ⑤存量撞名（段∈任何规则 original/nick——对齐
--   saveGroups foreign 集） ⑥残尾准入（首段≤2字且∈候选=切刀残尾伪候选：
--   勒多·马尔克斯=赫里内勒多·马尔克斯被「里」刀斩尾，原文 69 处全是子串
--   重叠无独立串，建组必活咬名） ⑦段歧义（段⊂候选中其他·全名：卡拉马佐夫/
--   尼古拉/阿玛兰妲 类家族姓与祖孙同名冲突） ⑧段重复防污染（对齐
--   expandRelatedNames：脏书重复串全跳）。
local function autoFillUncoveredGroups(groups, candidates, rules, scattered)
  if not candidates or #candidates == 0 then return groups or {}, 0 end
  -- foreign_orig：替换源撞名集（闸④包含消费 + 闸⑤选段）——规则 original 与 AI 组
  -- 成员名（未来规则的 original）。规则 nick 是替换目标不吃匹配，不进闸④——
  -- 否则「阿黛拉伊达·伊万诺夫娜 ⊃ 伊万(老三组昵称)」类子串误杀（fengari 实测）。
  -- foreign_nick：仅闸⑤选段撞名用（对齐 saveGroups 撞名集，防白建组）。
  local covered, foreign_orig, foreign_nick, used_nicks0 = {}, {}, {}, {}
  for _, r in ipairs(rules or {}) do
    -- original 不分 enabled 一律视为已覆盖：禁用规则多半是用户手动禁或串写链
    -- 禁——自动建组不复活历史决定（同名 original 会复用条目改 enabled）。
    if r.original and r.original ~= "" then
      covered[r.original] = true
      foreign_orig[r.original] = true
    end
    if r.nick and r.nick ~= "" then
      foreign_nick[r.nick] = true
      -- 昵称查重对齐 existing_nicks（仅 enabled——与 saveGroups 上游组装同语义）
      if r.enabled then used_nicks0[r.nick] = true end
    end
  end
  if groups then
    for _, g in ipairs(groups) do
      for _, n in ipairs(g.names or {}) do
        covered[n] = true
        foreign_orig[n] = true
      end
    end
  end
  local candset = {}
  for _, w in ipairs(candidates) do candset[w] = true end
  -- 闸⑦预计算：候选·全名的段归属（段 → 含它的全名集合）
  local seg_owners = {}
  for _, w in ipairs(candidates) do
    if w:find("·", 1, true) then
      local tmp = w:gsub("·", "\1")
      for seg in tmp:gmatch("[^\1]+") do
        seg_owners[seg] = seg_owners[seg] or {}
        seg_owners[seg][w] = true
      end
    end
  end
  groups = groups or {}
  local added = 0
  for _, F in ipairs(candidates) do
    -- 闸⑩（preFix19）：残尾剔除复燃防线——候选刚被 strip 剔名/散组（残尾/
    -- 称谓粘连/尊称外指），机械兜底不得把毒以单人组形态还回来
    -- （实机 穆泰瓦里·阿卜杜·萨姆德谢赫 AI 组散后 autoFill 复活实锤）。
    if scattered and scattered[F] then
      logger.info("KOAI NameReplace: 自动建组跳过(残尾剔除复燃) -", F)
    elseif F:find("·", 1, true) and not covered[F] then
      -- 字节安全切段（与扫描侧 flush/expandRelatedNames 同款：· gsub 成 \1）
      local segs = {}
      local tmp = F:gsub("·", "\1")
      for seg in tmp:gmatch("[^\1]+") do segs[#segs + 1] = seg end
      local dup = false
      for i = 1, #segs do
        for j = i + 1, #segs do
          if segs[i] == segs[j] then dup = true break end
        end
        if dup then break end
      end
      if dup or #segs < 2 then
        if dup then logger.info("KOAI NameReplace: 自动建组跳过(段重复) -", F) end
      else
      local first = segs[1]
      -- preFix22：段残尾检定——任一段含叠字或末段以高频动词收尾=切刀把
      -- 动词/拟声粘连进人名（实机 Cairo 嘉瓦德哈哈大 建组后 2 处啃伤原文），
      -- 整条候选跳过（音译名段内不该有叠字，通用不变量非列举）。
      -- preFix23：末段泛称尾（加泰罗尼亚小伙子 类描述短语）同跳。
      local residue = false
      for si = 1, #segs do
        if hasDoubledHan(segs[si]) or (si == #segs and (endsWithResidueVerb(segs[si]) or endsWithGenericTail(segs[si]))) then
          residue = true break
        end
      end
      if residue then
        logger.info("KOAI NameReplace: 自动建组跳过(残尾粘连) -", F)
      else
      -- 闸⑨（preFix18）：首段含称谓/场所粘连词——"炒货店老板艾布·赛利阿"
        -- "新郎赫利勒·肖克特"类扫描粘连串，整条跳过（实机 Cairo 自动建组毒例）
        local glue = firstTitleGlue(first)
        if glue then
          logger.info("KOAI NameReplace: 自动建组跳过(称谓粘连) -", F, "（首段含「" .. glue .. "」）")
        elseif utf8len(first) <= 2 and candset[first] then
          logger.info("KOAI NameReplace: 自动建组跳过(残尾伪候选) -", F)
        else
          -- 闸④包含消费（只查替换源撞名集）
          local consumed
          for r in pairs(foreign_orig) do
            if r ~= F and F:find(r, 1, true) then consumed = r break end
          end
          if consumed then
            logger.info("KOAI NameReplace: 自动建组跳过(包含消费) -", F, "⊃", consumed)
          else
            -- 昵称选择：末段优先→首段兜底（①②③⑤⑦在段检验里）
            local nick, nick_src
            local function try_seg(s)
              local len = utf8len(s)
              if len < 2 or len > 6 then return false end
              if isPatronymic(s) then return false end
              if CANDIDATE_STOPWORDS[s] then return false end
              if isHonorificNick(s) then return false end
              -- 尾词门（preFix19）：段以场所/阿拉伯尊称词收尾（实机 萨姆德谢赫/
              -- 萨布里贝克 当昵称落书毒）——尊称连写粘连不配当昵称，整条跳过
              if tailTitleGlue(s) then return false end
              if used_nicks0[s] then return false end
              if foreign_orig[s] or foreign_nick[s] then return false end
              local owners = seg_owners[s]
              if owners then
                for w2 in pairs(owners) do
                  if w2 ~= F then return false end
                end
              end
              return true
            end
            for i = #segs, 2, -1 do
              if try_seg(segs[i]) then nick = segs[i] nick_src = "末段" break end
            end
            if not nick and try_seg(first) then nick = first nick_src = "首段" end
            if nick then
              groups[#groups + 1] = { names = { F }, canonical = nick, auto = true }
              added = added + 1
              logger.info("KOAI NameReplace: 自动建组 -", F, "→", nick, "(", nick_src, ")")
            else
              logger.info("KOAI NameReplace: 自动建组跳过(无合法昵称) -", F)
            end
          end
        end
      end
    end
  end
  end
  if added > 0 then
    logger.info("KOAI NameReplace: 自动建组 =", added, "组（AI 漏组机械兜底）")
  end
  return groups, added
end

-- preFix17：AI 组残尾伪候选剔除（实机 BN 教训：AI 清单继承扫描器切刀伪串——
-- "勒多·马尔克斯"是"赫里内勒多·马尔克斯"的字面子串（69=69 纯重叠，原文无
-- 独立串），AI 当真名建组后"马尔克斯→勒多"活咬真名（真名变"赫里内勒多·
-- 勒多"）落书。r8 的闸⑥只守自动建组，AI 组不过那道闸——这里补齐。
-- 判定：组内含·叫法 n（≥6 字）被另一候选 c 严格包含时，n 与 c 的字面计数
-- 相等 → n 无独立出现（纯重叠）→ 伪候选；计数不等 → n 有独立出现 → 保留
--（"米特里·费奥多雷奇"⊃于垃圾"子德米特里·费奥多雷奇"但独立出现更多，
-- 不误杀）。剔名后组不足 2 人 → 整组散。返回剔除说明供日志。
local function stripResidueGroupNames(groups, candidates, original_file)
  if not groups or #groups == 0 then return groups or {}, {}, {} end
  if not candidates or #candidates == 0 then return groups or {}, {}, {} end
  if not original_file then return groups or {}, {}, {} end
  local candset = {}
  for _, w in ipairs(candidates) do candset[w] = true end
  local removed = {}
  -- preFix19：被剔名/散组名收集——autoFill 兜底以此跳过（否则"残尾剔除→散组
  -- →候选裸奔→自动建组复活"把毒以单人组形态还回来，实机 穆泰瓦里/萨布里贝克 实锤）
  local scattered = {}
  for gi = #groups, 1, -1 do
    local g = groups[gi]
    local bad, bad_kind, owner = {}, {}, {}
    local probes, probed = {}, {}
    local function probe(n, ref, kind)
      owner[n] = ref
      bad_kind[n] = kind
      if not probed[n] then probed[n] = true; probes[#probes + 1] = n end
      if not probed[ref] then probed[ref] = true; probes[#probes + 1] = ref end
    end
    local names = g.names or {}
    -- (a) 跨候选残尾：组内含·叫法 n(≥6字) 被更长候选 c 字面包含
    for _, n in ipairs(names) do
      if utf8len(n) >= 6 and n:find("·", 1, true) then
        for c in pairs(candset) do
          if c ~= n and #c > #n and c:find(n, 1, true) then
            probe(n, c, "纯子串重叠于")
            break
          end
        end
      end
    end
    -- (b) 组内自净（preFix18，实机 Cairo"侯赛因→侯赛"毒）：组内叫法 n 是
    --   组内更长叫法 m 的前缀且计数相等 = n 无独立出现（纯重叠残尾）→剔。
    --   真前缀叫法不受影响（"奥雷里亚诺"单用多于"奥雷里亚诺·布恩迪亚"重叠，
    --   计数必不等→保留）。
    for i = 1, #names do
      local n = names[i]
      if not probed[n] and utf8len(n) >= 2 then
        for j = 1, #names do
          local m = names[j]
          if m ~= n and #m > #n and m:sub(1, #n) == n then
            probe(n, m, "纯子串重叠于组内")
            break
          end
        end
      end
    end
    -- (c) 称谓尾（preFix18，实机"阿卜杜胡咖啡馆/宰格鲁勒帕夏"毒）：叫法以
    --   场所/阿拉伯尊称词收尾 → 直接剔（粘连串不配当 original，无需计数）
    for _, n in ipairs(names) do
      local tw = tailTitleGlue(n)
      if tw and not probed[n] then
        probe(n, tw, "称谓尾「" .. tw .. "」粘连")
      elseif tw and probed[n] and not bad_kind[n] then
        owner[n] = tw
        bad_kind[n] = "称谓尾「" .. tw .. "」粘连"
      end
    end
    -- (d) 尊称外指（preFix19，实机"乌姆·赫奈斐→艾米娜"毒：女仆高频独立人物
    --   162 次被 AI 并入主母组，替换后 162 处串染）。组内叫法以 乌姆·X/艾布·X
    --   （某人之母/父尊称）开头且 X 不是本组任何叫法 → 该尊称指向的人物另有
    --   其人 → 直接剔（无需计数）。X 在组内才保留（乌姆·玛丽娅/玛丽娅 同人组
    --   合法）。误剔方向=漏合并（尊称串保持原文显示），无串染，宁漏勿错。
    for _, n in ipairs(names) do
      -- Lua patterns 无 | 交替，三前缀分别匹配
      local x = n:match("^乌姆·(.+)$") or n:match("^艾布·(.+)$") or n:match("^阿布·(.+)$")
      if x and not probed[n] then
        local in_group = false
        for _, m in ipairs(names) do
          if m == x then in_group = true break end
        end
        if not in_group then
          probe(n, x, "尊称外指（乌姆/艾布·" .. x .. " 非本组人物）")
        end
      end
    end
    -- (e) 动词尾/泛称尾残渣（preFix23，实机"奥里维回答→奥里维答"16 处/
    --   "加泰罗尼亚小伙子→梅塞苔丝"5 处毒）：AI 组成员以动词/泛称人称收尾
    --   = 切刀残渣或描述短语，直接剔（无需计数，宁漏勿错）。
    --   preFix30（块 B3）续接：类别尾（支系/家族/爵士）同样不是具体人名，
    --   一并直接剔（LS 玛尔丹·维尔加支系、BN 弗朗西斯·德雷克爵士 实机毒）。
    for _, n in ipairs(names) do
      if not probed[n] then
        local vt = endsWithResidueVerb(n)
        if vt then
          probe(n, vt, "动词尾「" .. vt .. "」残渣")
        else
          local gt = endsWithGenericTail(n)
          if gt then
            probe(n, gt, "泛称尾「" .. gt .. "」")
          else
            local ct = endsWithCategoryTail(n)
            if ct then
              probe(n, ct, "类别尾「" .. ct .. "」非具体人名")
            end
          end
        end
      end
    end
    if #probes > 0 then
      local ok_c, counts = pcall(countWordOccurrences, original_file, probes)
      if ok_c and counts then
        for n, c in pairs(owner) do
          if bad_kind[n] == "纯子串重叠于" or bad_kind[n] == "纯子串重叠于组内" then
            -- 防零陷阱：对照串计数 >0 才可比（计数异常时不剔，宁漏勿错）。
            -- preFix19 差值判定：独立出现 = n − c ≤2 视为噪声级独立（实机
            -- 开罗 侯赛=527 vs 侯赛因=526，1 次独立不值得把 526 处统一改名；
            -- 真前缀昵称如 奥雷里亚诺 独立 200 次，差值悬殊照常保留）。
            local cn, cc = counts[n] or 0, counts[c] or 0
            if cc > 0 and cn >= cc and cn - cc <= 2 then
              bad[n] = true
            end
          else
            bad[n] = true -- 称谓尾/尊称外指粘连直接剔
          end
        end
      end
    end
    if next(bad) then
      local kept, stripped_b, has_outer = {}, {}, false
      for _, n in ipairs(names) do
        if not bad[n] then kept[#kept + 1] = n
        else
          scattered[n] = true
          if bad_kind[n] == "纯子串重叠于组内" then
            stripped_b[#stripped_b + 1] = n
          elseif bad_kind[n] == "纯子串重叠于" then
            has_outer = true  -- (a) 跨候选残尾：组被外部伪候选污染，不可转换
          end
          removed[#removed + 1] = (g.canonical or "?") .. " - 剔 " .. n
              .. "（" .. (bad_kind[n] or "纯子串重叠于") .. " " .. (owner[n] or "?") .. "）"
        end
      end
      if #kept >= 2 then
        g.names = kept
        if bad[g.canonical or ""] then g.canonical = kept[1] end
      else
        -- preFix21：组内自净散组转换——唯一幸存者 kept[1] 是本人物全称（候选
        -- 门槛保证 ≥2 次真实出现），被剔者是它的短形（(b) 前缀且计数相等 =
        -- 全书该短形从不独立出现）。旧行为整组散+闸⑩拉黑把真人全称一并封死
        -- （实机 叶菲姆·彼得罗维奇/阿黛拉伊达·伊万诺夫娜 每轮漏组，用户被迫
        -- 手动补同型规则）。转单人组保留，昵称=被剔短形，替换方向由 saveGroups
        -- 全闸链（撞名⑤/截断层③/尊称/父称）把关；被剔短形仍入 scattered，
        -- 闸⑩ 照常拦其以 original 形态复活。只信 (b) 且限 ·名完整首段：
        -- (a) 勒多·马尔克斯毒原型维持散组；侯赛之于侯赛因（无·）不转换。
        local nick_n
        if not has_outer and #stripped_b > 0 and kept[1] and kept[1]:find("·", 1, true) then
          local seg1 = kept[1]:match("^([^·]+)·")
          for _, n in ipairs(stripped_b) do
            if n == seg1 and (not nick_n or #n > #nick_n) then nick_n = n end
          end
        end
        if nick_n then
          g.names = kept
          g.canonical = nick_n
          removed[#removed + 1] = kept[1] .. " - 组内自净转换（preFix21）→ " .. nick_n
              .. "（单人组保留，原整组散）"
        else
          removed[#removed + 1] = (g.canonical or "?") .. " - 整组散（剔后不足 2 人）"
          if g.canonical then scattered[g.canonical] = true end
          table.remove(groups, gi)
        end
      end
    end
  end
  return groups, removed, scattered
end

-- 整组否决（宁全舍不半并）：组内任一两两叫法命中任一硬证据 → 该组整个
-- 不采纳。不做"拆组留半"——拆错边比不合并更糟（伊柳沙组拆错会把父亲
-- 28 处改名成儿子）。返回保留组列表与否决说明列表。
local function filterBogusGroups(groups, original_file)
  local notes = {}
  local kept = {}
  if type(groups) ~= "table" then return kept, notes end
  local full = nil
  if original_file then
    local ok_f, f = pcall(getBookFullText, original_file)
    if ok_f then full = f end
  end
  for _, g in ipairs(groups) do
    local names = g.names or {}
    local why = nil
    for i = 1, #names do
      if why then break end
      for j = 1, #names do
        if i ~= j then
          local a, b = names[i], names[j]
          if vetoPatronymicClash(a, b) then
            why = a .. " × " .. b .. "：同名异父称（V2 结构冲突）"
            break
          end
          if vetoPrefixStrip(a, b) then
            why = a .. " × " .. b .. "：绰号前缀剥除配裸名（V4 形态，裸名可能另有所指）"
            break
          end
          if vetoDualPatronymic(a, b) then
            why = a .. " × " .. b .. "：双父称冲突（V5，组内混入两代/两人的父称）"
            break
          end
          if full then
            if vetoKinshipEvidence(full, a, b) then
              why = a .. " × " .. b .. "：同句亲属同位（V1，如「A的儿子B」）"
              break
            end
            if vetoTitleClashEvidence(full, a, b) then
              why = a .. " × " .. b .. "：异称谓互动同句（V3，如「A神父…询问…B长老」）"
              break
            end
          end
        end
      end
    end
    if why then
      notes[#notes + 1] = "否决[" .. table.concat(names, "/") .. "] " .. why
    else
      kept[#kept + 1] = g
    end
  end
  return kept, notes
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
  -- 方案 A 负样本反馈：被硬证据否决的分组回喂给 AI（上限 20 条在存储端保证）。
  -- 00:00 实机教训（卡拉马佐夫重扫实锤）：①旧版否决段拼在 prompt 前部，被后置
  -- 的 237 词清单稀释，AI 无视——5 组错组原样重提；②旧措辞「严禁再提出相同或
  -- 近似的人物组合」过禁——连同一人物自身的合法纯组（费奥多尔·巴甫洛维奇/
  -- 老卡拉马佐夫）也吓没了，老卡整本书没有进组。
  -- 修复：否决段挪到清单之后（AI 注意力尾部）＋措辞改为「禁混组、允纯组」；
  -- 此处只加载数据与打日志（下轮归组日志可直接判定注入是否生效）。
  local veto_hist = {}
  pcall(function()
    veto_hist = loadVetoNotes(ui, original_file)
    logger.info("KOAI NameReplace: 否决历史加载 =", #veto_hist, "条")
  end)

  local prompt = table.concat(context_lines, "\n")
      .. "\n\n任务：仅从下面清单中挑出人名词条，把书中同一人物的不同叫法归为一组"
      .. "（全名、简称、小名、外号），用于全书统一人名。"
      .. "\n要求："
      .. "\n1. 优先使用清单中原样的写法；译名变体必须以书内实际写法为准。"
      .. "\n2. 注意：同一人物在不同译本中译名可能不同（如老卡拉马佐夫兄弟有荣如德译本"
      .. "「格露莘卡/斯乜尔加科夫」与其他译本「格鲁申卡/斯梅尔佳科夫」之别）。"
      .. "清单来自对本书的逐字扫描，是本书实际写法的最可靠依据；"
      .. "凡与你认知的通行译名不一致处，一律以清单为准。"
      .. "\n3. 清单是机械扫描的结果，可能漏掉出现次数少的稀有叫法。"
      .. "若你确信某写法在书中确实出现，可以把它加入 names 提名——"
      .. "系统会立即在书中逐字验证，实际出现 ≥2 次的写法才会保留，凭空捏造的会被剔除。"
      .. "值得提名的：著名人物的通称（如「老卡拉马佐夫」）、完整全名"
      .. "（名+父称+姓，如「费奥多尔·巴甫洛维奇·卡拉马佐夫」）、"
      .. "清单漏收的简称+父称组合变体（如「米嘉·费奥多罗维奇」——简称与父称"
      .. "各自常见但连用少见，机械清单常漏）以及小名与外号。"
      .. "\n4. 只报告把握很大的组合，宁漏勿错；不确定就不报。"
      .. "\n5. 严禁把不同人物合并；同名不同人必须分开。"
      .. "\n6. 严禁把称谓/泛称当人物叫法：「父亲/母亲/儿子/老头儿/老爷/太太/长老」这类"
      .. "词全书指人不定，绝不能入组——哪怕你确信书里这个词指的就是某人。"
      .. "\n7. 父子、兄弟、同族是不同人物，严禁混入同组（如上尉与其子）；"
      .. "父称（…维奇/…夫娜）只属于对应名字的人物，不得单独成组或张冠李戴。"
      .. "同名不同父称（如 伊万·伊万诺维奇 与 伊万·费奥多罗维奇）是两个人；"
      .. "同一教名配不同姓氏/外号（如两位女性都叫丽莎）也是不同人；"
      .. "两叫法同句呈「A的儿子B」「A向B忏悔」等两人互动形态时，绝不可并组。"
      .. "\n8. 严禁把绰号/称号前缀从全名头部剥掉去配裸名：「美人儿蕾梅黛丝」"
      .. "绝不能与「蕾梅黛丝」并组——裸名可能是另一个同书人物（如《百年孤独》"
      .. "里就有两个蕾梅黛丝），「俏姑娘X」同理不得剥成「X」；亲属序称除外"
      .. "（「二哥伊万」与「伊万」可以是同一人）。剥离后与清单其他词条撞形的"
      .. "组合一律放弃。"
      .. "\n9. 每组给出 canonical（组内最通用的叫法）和一句话判断理由。"
      .. "canonical／昵称一律**优先取人物的「名」**，不要取姓：全名「名·姓」"
      .. "（如 克利斯朵夫·克拉夫脱）取「克利斯朵夫」不取「克拉夫脱」；"
      .. "「名·父称·姓」取最常用的名或「名·父称」；只有全书始终以姓相称、"
      .. "该人物没有稳定使用的名时才用姓。"
      .. "\n10. 组数不设上限，按重要程度排序，值得归的都归——主要人物之外，"
      .. "反复出现的次要配角（长老、仆人、军官、官员、孩子、房东、神父等）"
      .. "也要归组；但宁缺毋滥，没有把握的人物不要硬凑。没有发现就输出 []。"
      .. "\n11. 严禁把职业/类别词粘进叫法：叫法里带着「教授／大叔／大婶／医生／"
      .. "老师／老板」这类**职业**尾的，要把它剥掉用干净的名字（「卡希里教授」这个人的"
      .. "叫法写「卡希里」）。但**凡原文形态里带着称谓/亲属/身份词的（公爵／伯爵／"
      .. "皇帝／小姐／夫人／先生／老爷／爵士／爷爷／奶奶／伯伯／叔叔／舅舅／公公／"
      .. "婆婆／少校／上校／医生／牧师／检察官／船长／管家／仆人／教士／支系／本人／"
      .. "三号……），一律不要拿它当可替换的原文形态，也不要把它简化成裸名**——"
      .. "「安德烈公爵」的叫法就是「安德烈公爵」，严禁简化成「安德烈」；「诺瓦蒂埃"
      .. "爷爷」「卡瓦尔坎蒂少校」「马奈特医生」「水手辛巴德」「乐队指挥某某」这类"
      .. "带身份词的形态根本不要归组，正文保持原文。叫法本身也**严禁是纯身份词**"
      .. "（不许把「检察官」「侯爵」「教士」当叫法）。"
      .. "\n12. 纯父称（…维奇／…夫娜／…耶芙娜／…奇）不是独立叫法，**严禁单独成组**，"
      .. "也严禁与含它的全名凑成一组。同一人物的全名、名段、爱称必须并进**同一组**，"
      .. "严禁把同一个人拆成多个组；每个叫法在整张表里**只能出现一次**，不得跨组重复。"
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

    -- 关联叫法展开（B 方案）：AI 调用前零 token 机械拆段 + plain≥2 硬验证。
    -- 缓存读取后现算（不动扫描缓存键），全文提取走 getBookFullText 会话缓存。
    local expanded = nil
    if original_file then
      setLoadingText("正在展开全名的关联叫法（零 token 机械验证）…")
      local ok_exp, res_exp = pcall(expandRelatedNames, candidates, original_file)
      expanded = ok_exp and res_exp or nil
    end

    local ok, result = pcall(function()
      local queryAI = require("ai_query")
      -- 两点关键（v2.0 真机复现实锤）：
      -- ①必须显式禁用思考：deepseek-v4-flash 默认推理且对"只输出 JSON"任务
      --   会推理到 token 耗尽（8192 时推理 8189），content 永远为空 → 归组失败；
      -- ②不设 max_tokens 上限，沿用全局 response_max_tokens。
      local user_content = prompt
          .. "\n\n书中实际出现的叫法清单（按出现频率降序）：\n" .. table.concat(candidates, "、")
      if expanded and #expanded > 0 then
        user_content = user_content
            .. "\n\n此外，以下叫法是从上述含「·」的全名机械拆出的名段，系统已逐字验证同样出现在本书，可视为清单词条使用。"
            .. "归组注意（preFix15 提案3）：名段大多是所属全名同一人物的简称，应与含它的那个全名放进同一组，"
            .. "不要把它单独成组或漏掉；只有确凿属于另一人物时才另立一组：\n"
            .. table.concat(expanded, "、")
      end
      -- 方案 A 负样本反馈：否决记录放清单之后（AI 注意力尾部，防被清单稀释）。
      if #veto_hist > 0 then
        user_content = user_content
            .. "\n\n【重要】以下是系统在本书中逐字验证后否决过的错误分组，本轮必须遵守：\n"
            .. table.concat(veto_hist, "\n")
            .. "\n遵守方式：被否决的组合里混入了不同人物的叫法，严禁再把它们放进同一组；"
            .. "否决不针对叫法本身——同一人物自己的多个叫法仍然应当成组。"
            .. "把被否决组合里误混的那个叫法剔除后，剩下的正确组合本轮应当照常提出。"
      end
      -- preFix18：文学圈领域提示——阿拉伯特征触发时注入（候选机械形态判定，
      -- 保守阈值 ≥3；俄苏/其他语种不注入，维持现状零扰动）。放注意力尾部。
      if detectArabicCandidates(candidates) then
        user_content = user_content
            .. "\n\n【本书判定为阿拉伯文学作品，额外遵守：】"
            .. "\n·「乌姆·X／艾布·X」是尊称（某人之母/父），可与其对应人物归组，"
            .. "但严禁把「乌姆」「艾布」单独当叫法或昵称。"
            .. "\n·「阿卜杜·X」是完整人名结构，严禁拆段；「阿卜杜」单用不是人名。"
            .. "\n·阿拉伯名库极窄（穆罕默德/艾哈迈德/阿里/哈桑等高频复用），"
            .. "含同名段的两个叫法若无同句证据（同句出现/亲属同位）严禁并组，宁漏勿错。"
            .. "\n·带职业/称谓前缀的串（如「炒货店老板××」「新郎××」）与带场所后缀的串"
            .. "（如「××咖啡馆」）是扫描粘连，严禁入组；「×谢赫／×帕夏／×贝克」尊称连写"
            .. "可归到本人，但不得当昵称，昵称优先用名（教名），无独立名时才用姓。"
      end
      return queryAI({
        { role = "system", content = "你是严谨的中文图书人物分析助手，只输出 JSON。优先使用用户清单中的词条；清单外的稀有叫法提名会被系统在书中逐字验证，捏造的将被剔除。" },
        { role = "user", content = user_content },
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
    logger.info("KOAI NameReplace: 解析有效组数 =", groups and #groups or 0)
    if groups and #groups > 0 then
      -- 越界过滤：组内只保留清单中真实存在的写法（含现有规则的原名/昵称）；
      -- 清单外的词（AI 提名的稀有叫法，如"老卡拉马佐夫"）当场解包全书逐字
      -- 验证，出现 ≥2 次才放行——文学知识补漏 + 本地硬验证双保险，
      -- AI 凭空捏造的译名无论多像都进不了规则
      local allowed = {}
      for _, w in ipairs(candidates) do allowed[w] = true end
      for _, w in ipairs(expanded or {}) do allowed[w] = true end
      for _, r in ipairs(rules) do
        allowed[r.original] = true
        allowed[r.nick] = true
      end
      local nominated, banned = {}, {}
      for _, g in ipairs(groups) do
        for _, n in ipairs(g.names or {}) do
          if not allowed[n] and n ~= "" and utf8len(n) >= 2 then
            -- 称谓/泛称（父亲/老头儿/老爷…）出现次数必然 ≥2，计数验证拦不住，
            -- 在此直接拒绝——AI 提名也进不了规则
            if CANDIDATE_STOPWORDS[n] then banned[#banned + 1] = n
            else nominated[n] = true end
          end
        end
        if g.canonical and g.canonical ~= "" and not allowed[g.canonical]
            and utf8len(g.canonical) >= 2 then
          if CANDIDATE_STOPWORDS[g.canonical] then banned[#banned + 1] = g.canonical
          else nominated[g.canonical] = true end
        end
      end
      if #banned > 0 then
        logger.info("KOAI NameReplace: 称谓/泛称提名拦截:", table.concat(banned, "/"))
      end
      local nom_list = {}
      for w in pairs(nominated) do nom_list[#nom_list + 1] = w end
      if #nom_list > 0 then
        table.sort(nom_list)
        logger.info("KOAI NameReplace: verifying", #nom_list, "nominated:", table.concat(nom_list, "/"))
        local ok_verify, counts = pcall(countWordOccurrences, original_file, nom_list)
        counts = ok_verify and counts or {}
        for _, w in ipairs(nom_list) do
          -- 方案 B：提名验证补形态门——计数验证拦不住书里真实存在的脏残尾
          -- （"子德米特里"5 次照过 ≥2 门），首尾洗刀/残尾守卫与扫描侧同语义
          local wash_b = false
          if utf8len(w) >= 6 then
            local h, t = utf8_head_tail(w)
            if HEAD_KNIFE[h] or TAIL_KNIFE[t] or isDotResidueTail(w) then wash_b = true end
          elseif isKinResidueHead(w) then
            wash_b = true
          end
          -- preFix18：称谓尾粘连（"阿卜杜胡咖啡馆/宰格鲁勒帕夏"类）提名拒收
          if tailTitleGlue(w) then wash_b = true end
          if wash_b then
            logger.info("KOAI NameReplace: nominated rejected(形态门):", w)
          elseif (counts[w] or 0) >= 2 then
            allowed[w] = true
            logger.info("KOAI NameReplace: nominated ok", w, "=", counts[w])
          else
            logger.info("KOAI NameReplace: nominated rejected", w, "=", counts[w] or 0)
          end
        end
      end
      -- 父称防线（v2.7.5 实机教训：AI 把纯父称词张冠李戴——"帕尔菲诺维奇→
      -- 斯乜尔加科夫""伊格纳启耶夫娜→莉兹"。父称词只有当组内存在以其结尾
      -- 或开头的完整名时才保留，否则剔除——宁漏勿错。对无父称的中文书零影响）
      -- 2026-09-27 二次实机教训：旧版把"名+父称"（含·，如 费奥多尔·巴甫洛维奇/
      -- 卡捷琳娜·伊万诺夫娜）也当父称杀——16 词误剔、320 次的"费奥多尔·
      -- 巴甫洛维奇"全书没被替换。现只拦"纯父称"（不含·，如 帕尔菲诺维奇/伊里奇），
      -- 且对应名检查改为前缀或后缀双向（伊里奇←彼得·伊里奇；费尧多罗维奇←
      -- 费尧多罗维奇·卡拉马佐夫）。isPatronymic 已提为文件级，供关联叫法展开共用。
      local filtered = {}
      for _, g in ipairs(groups) do
        local kept = {}
        for _, n in ipairs(g.names or {}) do
          if allowed[n] then kept[#kept + 1] = n end
        end
        -- preFix30（块 D）：父称组丢弃——整组除"纯父称"就是"含该父称的全名"、
        -- 且组选的 canonical 本身也没有新信息（就是某个父称，或含父称的那个全名）
        -- 时，这组只剩噪声。
        -- 实机 r30 KM 用户报"居然出现 93 组"，实测 114 组里约 52 组是这种：
        -- {伊万诺夫娜, 卡捷琳娜·伊万诺夫娜}→卡捷琳娜·伊万诺夫娜、{库兹米奇,
        -- 库兹马·库兹米奇}→库兹马·库兹米奇……它们在确认弹窗里逐条列出，用户
        -- 被迫一条条看，而规则本身要么倒置被拒（长→长），要么更糟（昵称落到短
        -- 父称上就把全名替换成父称）。
        -- ⚠ canonical 自指这一条不能省：全库反验显示只按"整组都是父称及其全名"
        -- 判会把 5 组**有效**规则连坐（QR 潘苔莱·普罗珂菲耶维奇→潘苔莱、
        -- AK 阿列克谢·亚历山德罗维奇→阿列克谢、WPa 安娜·帕夫洛夫娜→安娜，
        -- 它们的 canonical 是真正的简称，能正常替换）。加上自指条件后这 5 组
        -- 全部保持原行为。整组丢=零风险：该人物的正式叫法另有正常组照常替换。
        local canon_e = (g.canonical and g.canonical ~= "") and g.canonical or kept[1]
        local pats = {}
        for _, n in ipairs(kept) do
          if isPatronymicLoose(n) then pats[#pats + 1] = n end
        end
        local pat_group = false
        if #pats > 0 and canon_e then
          pat_group = true
          for _, n in ipairs(kept) do
            if not isPatronymicLoose(n) then
              local ok_m = false
              for _, p in ipairs(pats) do
                if #n > #p and (n:sub(-#p) == p or n:sub(1, #p) == p) then
                  ok_m = true
                  break
                end
              end
              if not ok_m then pat_group = false break end
            end
          end
          if pat_group then
            local self_ref = false
            for _, p in ipairs(pats) do
              if canon_e == p or (#canon_e > #p and canon_e:sub(-#p) == p) then
                self_ref = true
                break
              end
            end
            pat_group = self_ref
          end
        end
        if pat_group then
          logger.info("KOAI NameReplace: 父称组丢弃 - ", table.concat(kept, "/"),
            "（组内只剩父称与含它的全名，无可替换的独立叫法）")
          kept = {}
        end
        local final = {}
        for _, n in ipairs(kept) do
          if isPatronymic(n) then
            local hasFull = false
            for _, m in ipairs(kept) do
              if m ~= n and #m > #n
                and (m:sub(-#n) == n or m:sub(1, #n) == n) then hasFull = true break end
            end
            if not hasFull then
              logger.info("KOAI NameReplace: 父称无对应全名同组，剔除:", n)
              n = nil
            end
          end
          if n then final[#final + 1] = n end
        end
        kept = final
        if #kept >= 2 then
          filtered[#filtered + 1] = { names = kept, canonical = allowed[g.canonical] and g.canonical or kept[1], reason = g.reason or "" }
        end
      end
      groups = filtered
      logger.info("KOAI NameReplace: 清单过滤后组数 =", #groups)
      -- 硬证据否决层：全文缓存此时已热（关联展开/提名验证已解包过全书），
      -- 这里只补字节级查找。命中即整组否决（最坏后果=没合并），详见
      -- filterBogusGroups 注释——根治 AI 跨人错组（帕伊西→佐西马类）。
      if #groups > 0 and original_file then
        -- 静默复核（用户拍板 2026-09-27）：不弹进度框。纯本地机械查找，
        -- 本书约 5 秒且紧跟 AI 等待之后，静默无"冻屏"感知；早先版本此处弹
        -- timeout=nil 常驻框且无人收口，会悬停到手动点掉（实机泄漏），已移除。
        -- 复核异常走下方 err 日志，最坏=没复核，不比没有这层差。
        local ok_veto, kept_g, veto_notes = pcall(filterBogusGroups, groups, original_file)
        if ok_veto and type(kept_g) == "table" then
          for _, note in ipairs(veto_notes or {}) do
            logger.warn("KOAI NameReplace: 错组否决 - ", note)
          end
          if #(veto_notes or {}) > 0 then
            logger.info("KOAI NameReplace: 硬证据否决后组数 =", #kept_g,
              "（否决", #veto_notes, "组）")
            -- 方案 A 负样本反馈：否决记录入书侧车，下轮归组注入 prompt——
            -- 同形态组合 AI 不再提名，学费只交一次（pcall 保护，失败=没有反馈层）
            pcall(saveVetoFeedback, ui, original_file, veto_notes)
          end
          groups = kept_g
        else
          logger.err("KOAI NameReplace: 硬证据否决层异常，跳过复核:", kept_g)
        end
      end
    end
    -- preFix17：AI 组残尾伪候选剔除（实机 BN 教训：勒多·马尔克斯 活咬真名）。
    local residue_removed, scattered = {}, {}
    groups, residue_removed, scattered = stripResidueGroupNames(groups, candidates, original_file)
    for _, note in ipairs(residue_removed) do
      logger.info("KOAI NameReplace: AI 组残尾伪候选剔除 - ", note)
    end
    -- preFix16：AI 静默漏组机械兜底——未被任何组/规则覆盖的·候选自动建组。
    -- 放在零组早退之前：AI 零组时机械组也能撑起后续向导流程。
    -- preFix19：scattered（被剔名/散组名）随行——兜底不得复活刚被剔除的毒。
    local auto_added = 0
    groups, auto_added = autoFillUncoveredGroups(groups, candidates, rules, scattered)
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
    local existing_nicks = {} -- 现有规则全部昵称（自动昵称组间查重用）
    for _, r in ipairs(rules) do
      if r.enabled and r.nick ~= "" then
        existing_nick[r.original] = r.nick
        existing_nicks[r.nick] = true
      end
    end

    -- 保存函数：kept = { { g = 组, nick = 昵称(可空) }, ... }
    -- direct=true（仅"全部采纳"路径）：保存后跳过"是否立即应用"确认，直接应用
    -- preFix22：倒置检定（纯函数）——昵称比原名长=短→长倒置（AK 实机：裸名
-- 玛丽亚 被④档最长兜底倒置成 玛丽亚·叶夫根尼耶夫娜 落库，白名单前邻位冒领
-- 2+4 处）。拒绝该条规则（宁漏勿错，原名保持原文），不整组否决——组内其他
-- 长名→短形的合法规则照常落。
local function isInvertedNick(target, n)
  return target ~= nil and n ~= nil and #target > #n
end

-- preFix23：复姓连写自嵌套检定——原文存在 orig<连接符>nick 连写形态
-- （实机 JD 夏托—勒诺 ×147：切刀按 · 切不认破折号，复姓被拆成两个伪候选
-- 并组后规则在连写内部命中 → 勒诺—勒诺）。命中返回连写串，否则 nil。
-- getBookFullText 带缓存，批量规则创建时同一全文只解包一次。
local function compoundNestedBlocked(orig, nick, original_file)
  if not original_file or not orig or not nick or orig == "" or nick == "" then return nil end
  local probes = {}
  for conn in pairs(CONNECTOR_CHARS) do
    probes[#probes + 1] = orig .. conn .. nick
  end
  local ok_c, counts = pcall(countWordOccurrences, original_file, probes)
  if not (ok_c and counts) then return nil end
  for _, w in ipairs(probes) do
    if (counts[w] or 0) > 0 then return w end
  end
  return nil
end

-- preFix27：配偶称谓自嵌套检定——组内同时存在 A 与「A+亲属称谓尾」时，
-- 后者是前者的配偶/亲属而非本人（容德雷特 vs 容德雷特大娘）。命中返回 A，
-- 否则 nil。纯组内比对，无全文开销。
local function kinNestedBlocked(n, names)
  if not names then return nil end
  local kin = endsWithKinSuffix(n)
  if not kin then return nil end
  local a = n:sub(1, #n - #kin)
  if a == "" then return nil end
  for _, m in ipairs(names) do
    if m == a then return a end
  end
  return nil
end

local function saveGroups(kept, direct)
      local updated_rules = loadRules(ui, original_file)
      local added = 0
      local used_nicks = {}   -- 本次保存各组已占用昵称（组间查重，硬规则）
      local decided = {}      -- { names = ..., target = ... } 供撞形提示与 summary
      for _, item in ipairs(kept) do
        local g = item.g
        local nick = trim(item.nick or "")
        -- 目标名：填了昵称用昵称（用户显式指定，尊重不查重）；
        -- 留空走自动昵称分档（2026-09-27 新增组间查重硬规则）：
        --   ①组内已有昵称（同人物延续，豁免 existing_nicks 查重）
        --   ②canonical（非停用词）
        --   ③组内叫法按短→长（非停用词）
        --   ④最长叫法兜底
        -- 每档先过两道查重：本次保存其他组已占用（used_nicks）、已有规则昵称
        -- （existing_nicks，仅①档豁免）→ 撞了自动换下一档。兄弟同姓、两个人物
        -- 共用同一称呼等撞形由此自动根治。
        local target = nil
        local clash_blocked = nil  -- 提案1：被跨组撞名闸拦下的首个候选（日志/弹窗说明用）
        local trunc_blocked = nil  -- preFix18 层③：被前缀截断闸拦下的首个候选
        if nick ~= "" then
          target = nick
        else
          local existing_here = nil
          for _, n in ipairs(g.names) do
            if existing_nick[n] then existing_here = existing_nick[n] break end
          end
          local cands = {}
          if existing_here then cands[#cands + 1] = { v = existing_here, cont = true } end
          -- ②档防倒置（2026-09-27 实机教训）：规则被清空后①档全空，AI 的
          -- canonical="最通用叫法"往往就是原书全名，直接当昵称会把替换方向
          -- 反转成短名→长名（老卡拉马佐夫→费奥多尔·巴甫洛维奇·卡拉马佐夫，
          -- 文本膨胀 38741 字节且肉眼无变化）。canonical 只有不长于组内最短
          -- 叫法才可用，否则跳过交给③档短→长。且纯父称不当昵称（V5 闸 A，
          -- 2026-09-27：费尧多罗维奇 18B=老卡拉马佐夫 18B 等长穿透了长度门）。
          local shortest = nil
          for _, n in ipairs(g.names) do
            if not CANDIDATE_STOPWORDS[n] and (shortest == nil or #n < shortest) then
              shortest = #n
            end
          end
          -- preFix30（块 B4）：昵称半截闸——canonical 若是"更长称呼的碎片"
          -- （切刀产出的半截名），拿来当昵称会把正文写成残句。实机 r30 NGF/MQ
          -- 纳吉布：切刀表含「长」，「巴利探长」被切成「巴利探」充作候选，
          -- canonical=巴利探 落库后裸「穆赫辛」16 处全变「巴利探」→ 出现
          -- 「巴利探简直不敢相信」。旧版截断闸只查 original（不查 nick），
          -- 故这类"昵称本身半截"的毒一路畅通；此处用昵称侧判据（见函数注释：
          -- 不复用 preFix24 排除表，因它含"长/先"等头衔首字）补上。
          -- preFix30（块 B5）：称谓/职业尾剥离——canonical 或组内叫法以 教授/大叔/
          -- 大婶/大夫/医生/护士/老师/老板 收尾时，剥掉尾巴取短形当昵称候选
          -- （实机 NGF/MQ：canonical=「卡希里教授」「迈瓦希卜大叔」）。剥出的短形
          -- 必须在原文出现 ≥2 次才认（与提名同门槛，防剥出空壳）；不达标就不剥，
          -- 保持原状让后面的档位照常决定。
          local strip_map = {}   -- 原名 → 剥尾短形
          if g.canonical and g.canonical ~= "" then
            local h = stripTitleTail(g.canonical)
            if h then strip_map[g.canonical] = h end
          end
          for _, n in ipairs(g.names) do
            if not CANDIDATE_STOPWORDS[n] then
              local h = stripTitleTail(n)
              if h then strip_map[n] = h end
            end
          end
          local strip_ok = {}    -- 通过计数门的短形
          if next(strip_map) then
            local probe_list = {}
            for _, h in pairs(strip_map) do probe_list[#probe_list + 1] = h end
            local ok_s, sc = pcall(countWordOccurrences, original_file, probe_list)
            if ok_s and type(sc) == "table" then
              for _, h in pairs(probe_list) do
                if (sc[h] or 0) >= 2 then strip_ok[h] = true end
              end
            end
          end
          local canon_v = g.canonical
          if g.canonical and strip_map[g.canonical] then
            local h = strip_map[g.canonical]
            if strip_ok[h] then
              canon_v = h
              logger.info("KOAI NameReplace: 称谓尾剥离(canonical) - ", g.canonical, "→", h)
            end
          end
          local canon_frag = nil
          if canon_v and canon_v ~= "" then
            canon_frag = nickFragmentSuspect(original_file, canon_v)
          end
          if canon_frag then
            logger.info("KOAI NameReplace: 昵称半截拒绝(canonical) - ", canon_v,
              "（末字与原文后接字拼成头衔「", canon_frag, "」，判为名+头衔的半截）")
          end
          if canon_v and canon_v ~= "" and not CANDIDATE_STOPWORDS[canon_v]
              and not isPatronymic(canon_v)
              and not isHonorificNick(canon_v)
              and not canon_frag
              and shortest ~= nil and #canon_v <= shortest then
            cands[#cands + 1] = { v = canon_v, cont = existing_here == canon_v }
          end
          local sorted = {}
          for _, n in ipairs(g.names) do
            if not CANDIDATE_STOPWORDS[n] then
              -- 剥尾短形优先于原长形（先入列=先被选中）
              local h = strip_map[n]
              if h and strip_ok[h] and h ~= n then sorted[#sorted + 1] = h end
              sorted[#sorted + 1] = n
            end
          end
          table.sort(sorted, function(a, b) return #a < #b end)
          for _, n in ipairs(sorted) do
            cands[#cands + 1] = { v = n, cont = n == existing_here }
          end
          local longest = ""
          for _, n in ipairs(g.names) do
            if #n > #longest then longest = n end
          end
          if longest ~= "" then cands[#cands + 1] = { v = longest, cont = longest == existing_here } end
          -- A② 简繁昵称偏好：候选含繁体字形且组内存在逐字转简后的同形叫法
          -- → 繁体候选让位（只降级不删除——全书只有繁体写法时无孪生、照常
          -- 可用）。①档既有昵称（cont=true，用户手选）不参与让位。
          for _, c in ipairs(cands) do
            if not c.cont then
              local cv = toSimpName(c.v)
              if cv ~= c.v then
                for _, m in ipairs(g.names) do
                  if m == cv then c.trad = true break end
                end
              end
            end
          end
          -- 跨组撞名集（preFix15 提案1）：自动昵称的候选若与其他人物撞名，
          -- 选上去=本组规则昵称撞他组规则 original，串写链消毒会把本组规则整组
          -- 禁掉（百年孤独实锤：父亲组昵称=儿子裸名 何塞·阿尔卡蒂奥，父子显示
          -- 同串落书 20 html）。撞名集=其他保留组成员＋存量规则中不属本组的
          -- original/昵称；①档既有昵称（cont=true，同人物延续/用户手选）豁免。
          local foreign = {}
          do
            local in_group = {}
            for _, n in ipairs(g.names) do in_group[n] = true end
            for _, other in ipairs(kept) do
              if other.g ~= g then
                for _, n in ipairs(other.g.names) do foreign[n] = true end
              end
            end
            for _, r in ipairs(updated_rules) do
              local same = (r.original ~= nil and in_group[r.original] == true)
                  or (r.nick ~= nil and in_group[r.nick] == true)
              if not same and r.original and r.original ~= "" then
                foreign[r.original] = true
                if r.nick and r.nick ~= "" then foreign[r.nick] = true end
              end
            end
          end
          for _, c in ipairs(cands) do
            if not c.cont and foreign[c.v] then
              c.clash = true
              if clash_blocked == nil then clash_blocked = c.v end
            end
          end
          -- preFix18 层③：昵称前缀截断验证——候选若是组内更长叫法的真前缀且
          -- 原文无独立出现（计数相等），即残尾截断（开罗三部曲实机教训：AI
          -- canonical=侯赛 而组内只有侯赛因，strip 组内自净管不到 canonical-only
          -- 场景），拒绝当选交给下一档。真前缀昵称（奥雷里亚诺 独立高频出现，
          -- 计数 > 全名）不受影响。①档既有昵称（cont=true，历史延续/用户手选）
          -- 豁免。计数异常（全 0）不拦，宁漏勿错。
          local trunc_probes = {}
          for _, c in ipairs(cands) do
            if not c.cont then
              local w = c.v
              if w and #w >= 2 then
                for _, m in ipairs(g.names) do
                  if m ~= w and #m > #w and m:sub(1, #w) == w then
                    c.need_count = { w = w, m = m }
                    trunc_probes[#trunc_probes + 1] = w
                    trunc_probes[#trunc_probes + 1] = m
                    break
                  end
                end
              end
            end
          end
          if #trunc_probes > 0 and original_file then
            local ok_t, tc = pcall(countWordOccurrences, original_file, trunc_probes)
            if ok_t and type(tc) == "table" then
              for _, c in ipairs(cands) do
                if c.need_count then
                  local cw = tc[c.need_count.w] or 0
                  local cm = tc[c.need_count.m] or 0
                  -- preFix19 差值判定：独立出现 = w − m ≤2 视为噪声级独立
                  -- （实机开罗 侯赛=527 vs 侯赛因=526——1 次独立不值得把
                  -- 526 处统一改名；真前缀独立高频如 奥雷里亚诺 200 差照常可用）
                  if cw > 0 and cw >= cm and cw - cm <= 2 then
                    -- preFix21：·名完整首段豁免——w 是 m 首个 · 前的完整段
                    -- （叶菲姆 之于 叶菲姆·彼得罗维奇）= 名·父称 的正规短形，
                    -- 不是残尾截断，不拒（实机用户手动补 3 条同型规则实证需求；
                    -- 短形计数=全称说明全书无第二人叫此名，作输出无冒领）。
                    -- 阿拉伯尊称首段（乌姆/艾布/阿布…）已在②档入口被
                    -- isHonorificNick 拦下；侯赛之于侯赛因（无·）照旧拒。
                    local seg1 = c.need_count.m:match("^([^·]+)·")
                    if seg1 ~= c.need_count.w then
                      c.trunc = true
                      if trunc_blocked == nil then trunc_blocked = c.need_count.w end
                      logger.info("KOAI NameReplace: 昵称截断拒绝 - ", c.need_count.w,
                        "（为「", c.need_count.m, "」前缀且原文无独立出现，计数 ", cw, "=", cm, "）")
                    end
                  end
                end
              end
            end
          end
          for _, c in ipairs(cands) do
            if not c.trad and not c.clash and not c.trunc and not isHonorificNick(c.v)
                and not used_nicks[c.v] and (c.cont or not existing_nicks[c.v]) then
              target = c.v
              break
            end
          end
          -- 兜底收窄（preFix15 提案1）：g.canonical 不属本组成员，可能正是其他
          -- 人物的叫法（百年孤独实锤：父亲组 canonical=儿子裸名）→ 撞名时跳过；
          -- longest/g.names[1] 是本组成员，落上去只是对本人空操作，无害。
          local fallback_canon = g.canonical
          if fallback_canon and (fallback_canon == "" or foreign[fallback_canon]) then
            fallback_canon = nil
          end
          target = target or longest or fallback_canon or g.names[1]
          -- preFix30（块 C'）：名优先纠正（收窄版）——昵称取的是"姓"（组内某含·
          -- 全名的末段）时改用"名"。实机 r30 用户点名：JC 约翰·克里斯朵夫主角被
          -- 简略成姓「克拉夫脱」（原书仅 61 次），而名「克利斯朵夫」4869 次。
          -- ⚠ 必须收窄成"以本组叫法为准"：更宽的"谁出现得多就用谁"写法已被反向
          -- 验证否决（全库 11 书 290 条启用规则上会改 35 组，其中 34 组是错的——
          -- BN 特里斯特/森特诺/阿玛多/塞拉多 全被并成「奥雷里亚诺」、Cairo 十余组
          -- 同型坍缩、KM 米乌索夫→彼得）。收窄后全库只命中 10 组，方向全是
          -- "姓→名"、无一处误伤。四个收窄条件：
          --   ① target 确实是组内某含·全名的末段（爱称/尊称天然不受影响）
          --   ② 改用后的"名"必须**本身是本组已确认的叫法**（不是机械拆段裸奔产物）
          --   ③ 该名在原文的出现次数确实多于姓
          --   ④ 该名不是他组叫法（foreign）、不是本次已占用昵称、不是纯尊称
          -- 只改昵称不改 original，替换方向不变。
          if target and target ~= "" and original_file then
            local surname_full = nil
            for _, n in ipairs(g.names) do
              if type(n) == "string" and n:find("·", 1, true) and #n > #target
                  and n:sub(-(#target + 2)) == "·" .. target then
                surname_full = n
                break
              end
            end
            local first = surname_full and surname_full:match("^([^·]+)·") or nil
            local first_in_group = false
            if first then
              for _, n in ipairs(g.names) do
                if n == first then first_in_group = true break end
              end
            end
            if first and first_in_group and #first >= 2 and first ~= target
                and not foreign[first] and not used_nicks[first]
                and not CANDIDATE_STOPWORDS[first] and not isHonorificNick(first) then
              local ok_p, pc = pcall(countWordOccurrences, original_file, { target, first })
              if ok_p and type(pc) == "table" then
                local cs, cf = pc[target] or 0, pc[first] or 0
                if cf > cs then
                  logger.info("KOAI NameReplace: 名优先纠正 - ", target, "→", first,
                    "（昵称取的是姓，原文 ", cs, " 次 < 名 ", cf, " 次）")
                  target = first
                end
              end
            end
          end
        end
        used_nicks[target] = true
        if clash_blocked then
          logger.info("KOAI NameReplace: 跨组撞名降级", clash_blocked, "→", target,
              "（候选与其他人物叫法撞名，已跳过）")
        end
        decided[#decided + 1] = { names = g.names, target = target, clash_blocked = clash_blocked, trunc_blocked = trunc_blocked }
        local inversion_blocked = nil
        local compound_blocked = nil
        local fragment_blocked = nil
        local kin_blocked = nil       -- preFix27：配偶称谓闸拦下的首个叫法
        local kin_owner = nil         -- 其对应的本人叫法（日志说明用）
        local guard_blocked = nil     -- preFix32：短语/称谓守卫拦下的首个叫法
        local guard_kind = nil        -- 其拒绝原因（日志说明用）
        local cut_blocked = nil       -- preFix36：昵称砍切闸拦下的首个叫法
        for _, n in ipairs(g.names) do
          if n ~= target then
            -- preFix36：昵称砍切闸——target 是 n 挖掉一块的残渣（拿破仑→破仑
            -- 全书 522 处实锤），切点不在 · 分段边界一律不建，n 保持原文
            -- （宁漏勿错）。合法形态（·段/逐级前缀组合）不受影响。
            if subStrCutBlocked(n, target) then
              if cut_blocked == nil then cut_blocked = n end
            -- preFix22：倒置硬门——昵称比原名长的规则一律不建（宁漏勿错）
            elseif isInvertedNick(target, n) then
              if inversion_blocked == nil then inversion_blocked = n end
            elseif target and target ~= "" then
            -- preFix23：复姓连写自嵌套闸——原文存在 n<连接符>target 连写
            -- （夏托—勒诺 147 处实锤）= n 是复姓前半非独立叫法，建 n→target
            -- 必在连写内部命中产生「勒诺—勒诺」。拒建该条，宁漏勿错。
            local conn_hit = compoundNestedBlocked(n, target, original_file)
            if conn_hit then
              if compound_blocked == nil then compound_blocked = n end
            else
            -- preFix24：真名截断闸——n 若是"更长固定串的碎片"（切刀产出的半截名
            -- 冒充独立叫法，实机 查尔斯·达/庇拉尔·特尔/谢尔盖·伊万 三毒），
            -- 建 n→target 必在真名内部命中、把正文咬成残句，拒建该条（宁漏勿错）。
            local frag_c = truncationSuspect(original_file, n)
            if frag_c then
              if fragment_blocked == nil then fragment_blocked = n end
            else
            -- preFix27：配偶称谓闸——n 是组内 A 的亲属称谓形态（容德雷特大娘
            -- 之于容德雷特），建 n→target 会把妻子改成丈夫的名字，拒建该条，
            -- n 保持原文（仍由 A 的规则自然覆盖为「德纳大娘」可区分）。
            local kin_a = kinNestedBlocked(n, g.names)
            if kin_a then
              if kin_blocked == nil then kin_blocked = n end
              if kin_owner == nil then kin_owner = kin_a end
            else
            -- preFix32：短语/称谓守卫——短语残渣（皮埃尔觉得/到皮埃尔）、
            -- 爵位剥除（安德烈公爵→安德烈）、裸父称（安德烈伊奇→安德烈）
            -- 一律不建规则，称谓与短语保持原文（宁漏勿错）。
            local gk = ruleGuardSuspect(n, target)
            if gk then
              if guard_blocked == nil then guard_blocked = n end
              if guard_kind == nil then guard_kind = gk end
            else
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
            end
            end
            end
          end
        end
        if cut_blocked then
          decided[#decided].cut_blocked = cut_blocked
          logger.info("KOAI NameReplace: 昵称砍切拒绝 - ", cut_blocked,
            "→", target, "（昵称是原名挖掉一块的残渣且切点不在分段边界，"
            .. "建规则会把完整名啃短，不建宁漏勿错）")
        end
        if guard_blocked then
          decided[#decided].guard_blocked = guard_blocked
          logger.info("KOAI NameReplace: 短语/称谓守卫拒绝 - ", guard_blocked,
            "→", target, "（", guard_kind, "，不建规则宁漏勿错）")
        end
        if inversion_blocked then
          logger.info("KOAI NameReplace: 昵称倒置拒绝 - ", inversion_blocked,
            "→", target, "（昵称比原名长，不建规则宁漏勿错）")
        end
        if fragment_blocked then
          decided[#decided].fragment_blocked = fragment_blocked
          logger.info("KOAI NameReplace: 疑似半截名拒绝 - ", fragment_blocked,
            "→", target, "（原名在原文几乎总跟着同一个字，判为更长叫法的碎片，"
            .. "建规则会咬伤真名，不建宁漏勿错）")
        end
        if compound_blocked then
          logger.info("KOAI NameReplace: 复姓连写拒绝 - ", compound_blocked,
            "→", target, "（原文存在「", compound_blocked, "＋连接符＋", target,
            "」连写，原名是复姓前半非独立叫法）")
        end
        if kin_blocked then
          decided[#decided].kin_blocked = kin_blocked
          logger.info("KOAI NameReplace: 配偶称谓拒绝 - ", kin_blocked,
            "→", target, "（组内另有「", kin_owner or "?", "」，该叫法是亲属称谓"
            .. "不属本人，建规则会让配偶被改成本人的名字，不建宁漏勿错）")
        end
      end
      if added == 0 then
        UIManager:show(InfoMessage:new { text = "没有需要合并的组合。", timeout = 4 })
        return
      end
      -- 称谓化撞形提示（软）：昵称在原文以「X先生/X太太/老X」等形态出现时，
      -- 该称呼可能另有归属（实机案例："米乌索夫先生"是阿黛拉伊达之父而非
      -- 彼得·米乌索夫本人）。只提示不阻断——原文姓称呼多数就是本人（原著对
      -- 彼得即通称姓），黑箱自动改名会把正确昵称改坏。批量一次计数（走全文缓存）。
      local clash_by_nick = {}
      do
        local probes, owner = {}, {}
        for _, d in ipairs(decided) do
          local t = d.target
          if t and t ~= "" and clash_by_nick[t] == nil then
            clash_by_nick[t] = false
            for _, s in ipairs({ "先生", "太太", "夫人", "小姐", "大叔", "大婶", "少爷" }) do
              local p = t .. s
              probes[#probes + 1] = p
              owner[p] = t
            end
            local p2 = "老" .. t
            probes[#probes + 1] = p2
            owner[p2] = t
          end
        end
        if #probes > 0 then
          local ok_c, counts = pcall(countWordOccurrences, original_file, probes)
          if ok_c and counts then
            for _, p in ipairs(probes) do
              if (counts[p] or 0) > 0 then
                clash_by_nick[owner[p]] = true
                logger.info("KOAI NameReplace: 昵称撞形提示", p, "=", counts[p])
              end
            end
          end
        end
      end
      -- preFix33：裸姓共姓软提示——裸姓 n（不含·、≥2 汉字、非父称、非老/小/大
      -- 开头）被改成叫法 t 时，若原文另有「n伯爵/n公爵/n家」这类称谓/家族用法，
      -- 裸姓可能也指长辈或全家（WPa 实锤：别祖霍夫→皮埃尔 会让老伯爵被叫成
      -- 儿子；博尔孔斯基→安德烈 同理）。机械上无法区分「裸姓指本人」和「裸姓
      -- 指长辈」（硬闸反验会误伤 卡列尼娜→安娜/奥勃朗斯基→斯捷潘 等主规则），
      -- 故只提示不阻断：确认清单里标 ⚠，用户自行斟酌/事后在别名列表停用。
      local bare_hit = {}
      do
        local probes, owner = {}, {}
        for _, d in ipairs(decided) do
          for _, n in ipairs(d.names) do
            if type(n) == "string" and not n:find("·", 1, true) and utf8len(n) >= 2
                and not isPatronymicLoose(n) then
              local h = n:sub(1, 3)
              if h ~= "老" and h ~= "小" and h ~= "大" then
                -- preFix35：探针从 8 个爵位词扩到 20 个高频称谓（先生/夫人/
                -- 医生/少校/船长…此前裸姓+这些称谓的组合不产生提示）
                for _, s in ipairs({ "伯爵", "公爵", "男爵", "子爵", "侯爵",
                    "老爷", "少爷", "家", "先生", "夫人", "太太", "小姐",
                    "医生", "大夫", "少校", "上校", "中校", "船长", "牧师",
                    "神父", "将军", "警长", "探长", "爷爷", "奶奶", "叔叔",
                    "伯伯", "舅舅" }) do
                  local p = n .. s
                  probes[#probes + 1] = p
                  owner[p] = { d = d, n = n }
                end
              end
            end
          end
        end
        if #probes > 0 then
          local ok_c, counts = pcall(countWordOccurrences, original_file, probes)
          if ok_c and counts then
            for _, p in ipairs(probes) do
              local o = owner[p]
              if o and bare_hit[o.d] == nil and (counts[p] or 0) > 0 then
                bare_hit[o.d] = o.n .. "（如「" .. p .. "」×" .. counts[p] .. "）"
                logger.info("KOAI NameReplace: 裸姓共姓提示", p, "=", counts[p])
              end
            end
          end
        end
      end
      local summary = {}
      for _, d in ipairs(decided) do
        local line = table.concat(d.names, "/") .. " → " .. d.target
        -- 倒置防呆（2026-09-27 实机教训）：昵称比组内最短叫法还长 =
        -- 替换方向可疑（短名→长名，文本膨胀且肉眼无变化），弹窗标 ⚠。
        local shortest_d = nil
        for _, n in ipairs(d.names) do
          if shortest_d == nil or #n < shortest_d then shortest_d = #n end
        end
        if shortest_d ~= nil and #d.target > shortest_d then
          line = line .. "\n    ⚠ 昵称比组内最短叫法长，替换方向可疑（若非有意请在输入框改名）"
        end
        if clash_by_nick[d.target] then
          line = line .. "\n    ⚠ 原文另有「" .. d.target .. "」的称谓化用法（先生/太太等），若指他人可稍后在别名列表改名"
        end
        if bare_hit[d] then
          line = line .. "\n    ⚠ 裸姓「" .. bare_hit[d] .. "」在原文另有称谓/家族用法，可能也指长辈或全家；"
              .. "替换后若发现长辈被叫成本人名，可在别名列表停用该条"
        end
        if d.clash_blocked then
          line = line .. "\n    ※ 候选昵称「" .. d.clash_blocked .. "」与其他人物叫法撞名，已自动改用「" .. d.target .. "」"
        end
        if d.trunc_blocked then
          line = line .. "\n    ※ 候选昵称「" .. d.trunc_blocked .. "」为组内其他叫法的前缀且原文无独立出现，已自动改用「" .. d.target .. "」"
        end
        if d.fragment_blocked then
          line = line .. "\n    ※ 叫法「" .. d.fragment_blocked .. "」在原书中几乎总跟着同一个字，判为更长叫法的碎片（切字残留），该条未建规则、原文保持不变"
        end
        summary[#summary + 1] = line
      end
      local function doSaveAndAsk(direct)
        saveRules(ui, original_file, updated_rules)
        -- preFix17：全部采纳（昵称自动）不再二次弹"是否立即应用"——用户选
        -- 全部采纳即意图一步到位，弹窗多余；决策明细（含 ⚠ 提示）落日志可查，
        -- 直接应用重载（applyAndReload 自带进度框）。逐组确认路径维持原确认。
        if direct then
          for _, line in ipairs(summary) do
            logger.info("KOAI NameReplace: 全部采纳决策 - ", line)
          end
          NameReplace.applyAndReload(ui)
          return
        end
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
      -- （preFix15 提案2）A① 互为前缀预警弹窗已移除：r7 实机 18 对全为合法纯组
      -- （同一人物的两种写法），弹窗抓不住毒只添堵；两代同名混组的防线由
      -- saveGroups 的跨组撞名降级闸（提案1）接管。恢复直连保存确认。
      doSaveAndAsk(direct)
    end

    -- 全部采纳：所有组直接用自动昵称保存；direct=true 保存后跳过"是否立即
    -- 应用"二次确认直接应用重载（preFix17，用户拍板：该弹窗多余）
    local function adoptAll()
      local kept = {}
      for _, g in ipairs(groups) do
        kept[#kept + 1] = { g = g, nick = "" }
      end
      saveGroups(kept, true)
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

-- v2.7.5：设定新昵称的落盘前判定（纯函数，供 harness 单测）。
-- target_keys = 该人物全部规则的 original 集合；new_nick = 用户输入的新昵称。
-- 返回：count=目标规则数；same=全组昵称已等于新值（空操作；仅 count>0 时有意义，
--       count=0 恒为 false）；
--       other_orig=与他组规则原名同形（应用时串写防线会停用对方）；
--       other_nick=与他组昵称同形（列表将合并为同一人物显示）；
--       own_orig=本组内有原名=新值的规则（将退化为原名=昵称的空操作）。
local function classifyNickRename(rules, target_keys, new_nick)
  local out = { count = 0, same = true, own_orig = false, other_orig = {}, other_nick = {} }
  if type(rules) ~= "table" or type(target_keys) ~= "table" then
    out.same = false
    return out
  end
  for _, r in ipairs(rules) do
    if target_keys[r.original] then
      out.count = out.count + 1
      if r.nick ~= new_nick then out.same = false end
      if r.original == new_nick then out.own_orig = true end
    elseif r.original == new_nick then
      out.other_orig[#out.other_orig + 1] = r.original
    elseif r.nick == new_nick then
      out.other_nick[#out.other_nick + 1] = r.nick
    end
  end
  if out.count == 0 then out.same = false end -- 空组无"全组同昵称"可言
  return out
end

-- ============ preFix39：规则显示层治理（不改侧车底层） ============
-- 背景（09-30 实机 + 13 本离线体检）：AI 会产出两类"看起来是规则、实际匹配不到
-- 任何正文"的条目，用户界面上显得人物叫法很丰满，实际只有少数几条在工作：
--   (1) 语序倒装：本译本用「姓·名」写法（顿河 麦列霍夫·葛利高里 13 次、
--       呼啸山庄 厄恩肖·哈雷顿），AI 按中式语序写成「葛利高里·麦列霍夫」→
--       原样 0 命中。13 本全量实测 7 条，对调判据零误杀（83 条普通译名用字差异
--       如 费奥↔费尧 对调后同样查不到，不进此判据）。
--   (2) 纯空头：AI 按世界知识编的组合（葛利申卡 / 葛利高里·麦列霍夫 等），
--       原文任何写法都查不到、对调也查不到 → 永远匹配不到正文。
-- 处理：①倒装能救回的，在显示层"就地纠正"（只改显示、不写侧车，避免未应用
--       状态被改动的额外风险）；②其余查不到的，显示层过滤不列出。底层 sidecar
--       一律不动——保持"规则=用户与AI的共同产物"的原始记录，随时可回滚。

-- 规则名是否在原文可定位（含倒装纠正）。返回：hit(原文原样命中次数), corrected(纠正后写法 or nil)
local function locateRuleName(text, orig)
  if not text or orig == "" then return 0, nil end
  local whole = 0
  local pos = 1
  while true do
    local p = text:find(orig, pos, true)
    if not p then break end
    whole = whole + 1
    pos = p + 1
  end
  if whole > 0 then return whole, nil end
  -- 字节安全切段（与 expandRelatedNames 同款：·(C2 B7) 整体 gsub 成 \1）
  local tmp = orig:gsub("·", "\1")
  local segs = {}
  for s in tmp:gmatch("[^\1]+") do segs[#segs + 1] = s end
  if #segs < 2 then return 0, nil end
  -- 对调（2 段互换 / 3 段以上反转）后能命中 → 判为语序倒装
  local rev = {}
  for i = #segs, 1, -1 do rev[#rev + 1] = segs[i] end
  local cand = table.concat(rev, "·")
  if text:find(cand, 1, true) then return 0, cand end
  return 0, nil
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
  -- preFix39：原文存在性体检（仅用于显示层）。取全文一次（函数内有缓存）。
  local full_text = getBookFullText(original_file)
  local corrected_of, dead_of = {}, {}
  if full_text then
    for _, r in ipairs(rules) do
      local hit, corrected = locateRuleName(full_text, r.original or "")
      if hit == 0 then
        if corrected then corrected_of[r.original] = corrected
        else dead_of[r.original] = true end
      end
    end
  end

  -- v1.38：按人物（昵称）分组——一次合并会产生多条规则（各变体 → 同一昵称）
  -- preFix39：分组时先剔除"查无此名"的空头规则（仅显示层，底层 sidecar 不动）；
  -- 倒装可救回的保留在组内并标注。
  local persons, order = {}, {}
  local hidden_count = 0
  for _, rule in ipairs(rules) do
    if dead_of[rule.original] then
      hidden_count = hidden_count + 1
    else
      local key = rule.nick ~= "" and rule.nick or rule.original
      if not persons[key] then
        persons[key] = { nick = key, rules = {} }
        order[#order + 1] = key
      end
      table.insert(persons[key].rules, rule)
    end
  end

  local items = {}
  -- v2.7.5：全局批量删除（用户反馈逐个人物删太麻烦）。
  -- 放列表首位 + 分隔线；应用是"从原书备份重建"式，删空规则再应用 = 全书恢复原文
  table.insert(items, {
    text = "删除所有人物全部别名",
    separator = true,
    callback = function()
      local rules_now = loadRules(ui, original_file)
      if #rules_now == 0 then
        UIManager:show(InfoMessage:new { text = "当前没有任何别名规则。", timeout = 4 })
        return
      end
      local persons = {}
      local any_enabled = false
      for _, r in ipairs(rules_now) do
        persons[r.nick ~= "" and r.nick or r.original] = true
        if r.enabled then any_enabled = true end
      end
      UIManager:show(ConfirmBox:new {
        text = "删除本书全部别名？\n共 " .. #rules_now .. " 条规则、"
            .. (function()
              local n = 0
              for _ in pairs(persons) do n = n + 1 end
              return n
            end)() .. " 个人物。"
            .. (any_enabled
                and "\n\n删除后请点\"立即应用\"重载：全书所有人名恢复原文。"
                or  "\n\n当前所有规则均为停用状态，正文本就未替换，删除后无需重新应用。"),
        ok_text = "全部删除",
        ok_callback = function()
          -- 以落盘实时状态再判定（菜单快照可能过期），与"删除此人物"同策略
          local latest = loadRules(ui, original_file)
          local still_enabled = false
          for _, r in ipairs(latest) do
            if r.enabled then still_enabled = true break end
          end
          saveRules(ui, original_file, {})
          if still_enabled then
            offerApplyAfterRuleChange(ui, original_file)
          else
            UIManager:show(InfoMessage:new {
              text = "已删除全部别名规则。",
              timeout = 4,
            })
          end
        end,
      })
    end,
  })
  for _, key in ipairs(order) do
    local person = persons[key]
    local originals = {}
    for _, r in ipairs(person.rules) do
      if r.original ~= person.nick then originals[#originals + 1] = r.original end
    end
    local sub_items = {
      {
        -- v2.7.5：设定新昵称（用户需求 2026-09-27：「阿辽沙→卡老三」一键改名）。
        -- 一键把该人物全部规则的昵称统一改成新值；只动 nick 不动 original：
        -- 替换对象不变，仅改书内显示与 AI 称呼。pending 标记 + 生效签名含 nick
        -- （original\1nick），应用前提及扫描自动回退全量叫法检索，无需额外处理。
        text = "设定新昵称（一键改名）",
        callback = function()
          local person_label = person.nick ~= "" and person.nick or (originals[1] or "该人物")
          local dialog
          dialog = MultiInputDialog:new {
            title = "设定「" .. person_label .. "」的新昵称",
            fields = {
              {
                text = person.nick,
                -- 坑（09-27 实机闪退实锤）：此处位于 for _, key in ipairs(order) 循环体内，
                -- gettext 的 _ 被循环下标变量遮蔽（upvalue 为 number），调 gettext 即崩
                -- （attempt to call upvalue '_'，crash.log L16183 堆栈实锤）。
                -- 本函数作用域内字符串一律裸中文，禁用 gettext 包裹。
                hint = "新昵称（该人物全部叫法将统一替换为此称呼）",
              },
            },
            buttons = {
              {
                {
                  text = "取消",
                  callback = function()
                    UIManager:close(dialog)
                  end,
                },
                {
                  text = "保存",
                  is_enter_default = true,
                  callback = function()
                    local fields = dialog:getFields()
                    local new_nick = trim(fields[1] or "")
                    UIManager:close(dialog)
                    if new_nick == "" then
                      UIManager:show(InfoMessage:new { text = "新昵称不能为空。", timeout = 3 })
                      return
                    end
                    -- 以落盘实时状态重新定位（菜单快照可能过期），与"删除此人物"同策略
                    local rules_now = loadRules(ui, original_file)
                    local target_keys = {}
                    for _, r in ipairs(person.rules) do target_keys[r.original] = true end
                    local verdict = classifyNickRename(rules_now, target_keys, new_nick)
                    if verdict.count == 0 then
                      UIManager:show(InfoMessage:new { text = "未找到该人物的规则，可能已被删除。", timeout = 4 })
                      return
                    end
                    if verdict.same then
                      UIManager:show(InfoMessage:new { text = "新昵称与当前昵称相同，无需修改。", timeout = 4 })
                      return
                    end
                    -- 撞形软提示（不阻断）：跨组原名同形 → 应用时串写防线会停用对方；
                    -- 本组原名同形 → 该条规则退化为原名=昵称的空操作；跨组昵称同形 → 列表合组。
                    local warn = ""
                    if #verdict.other_orig > 0 then
                      warn = warn .. "\n\n注意：「" .. new_nick .. "」同时是这些规则的原名："
                          .. table.concat(verdict.other_orig, "、")
                          .. "。\n应用时串写防线会自动停用上述规则（防二次改写，其原名保持原文不替换）。"
                    elseif verdict.own_orig then
                      warn = warn .. "\n\n注意：「" .. new_nick .. "」也是该人物自己的原名之一，"
                          .. "那条规则将变成原名=昵称（实际不产生替换）。"
                    end
                    if #verdict.other_nick > 0 then
                      warn = warn .. "\n\n注意：已有其他人物使用昵称「" .. new_nick .. "」，"
                          .. "保存后两组会在别名列表合并为同一人物显示。"
                    end
                    UIManager:show(ConfirmBox:new {
                      text = "把「" .. person_label .. "」的 " .. verdict.count .. " 条叫法统一改为「" .. new_nick .. "」？\n"
                          .. "涉及原名：" .. (table.concat(originals, "、") ~= "" and table.concat(originals, "、") or "（无）")
                          .. "\n\n保存后请点\"立即应用\"重载本书，书内与 AI 回答即使用新昵称。"
                          .. warn,
                      ok_text = "保存",
                      ok_callback = function()
                        -- 确认框期间规则可能又变，再读一次落盘实时状态
                        local latest = loadRules(ui, original_file)
                        local n = 0
                        for _, r in ipairs(latest) do
                          if target_keys[r.original] then
                            r.nick = new_nick
                            r.pending = true -- v1.37：改动待生效
                            n = n + 1
                          end
                        end
                        saveRules(ui, original_file, latest)
                        if n > 0 then
                          offerApplyAfterRuleChange(ui, original_file)
                        end
                      end,
                    })
                  end,
                },
              },
            },
          }
          UIManager:show(dialog)
          dialog:onShowKeyboard()
        end,
      },
      {
        -- 一键暂停/恢复该人物全部别名（规则保留/重新启用）
        text_func = function()
          local any_enabled = false
          for _, r in ipairs(person.rules) do
            if r.enabled then any_enabled = true break end
          end
          -- v2.7.5 文案（用户指示 09-27）：「暂停替换此人物（规则保留，可恢复）」→「暂停别名合并」
          return any_enabled and "暂停别名合并" or "恢复别名合并"
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
        text = "删除别名合并",
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
        local label = person.nick .. "（原名：" .. (table.concat(originals, "、") ~= "" and table.concat(originals, "、") or "无") .. "）"
        -- preFix39：倒装可救回的条目在标签上标注原文语序（仅提示，不改侧车）
        local fixed = {}
        for _, r in ipairs(person.rules) do
          local c = corrected_of[r.original]
          if c then fixed[#fixed + 1] = r.original .. " → " .. c end
        end
        if #fixed > 0 then
          label = label .. "\n  ⚠ 原文语序为：" .. table.concat(fixed, "；")
        end
        return label
      end,
      sub_item_table = sub_items,
    })
  end
  -- preFix39：把被过滤掉的空头规则条数透明告知（用户可据此判断 AI 产出质量）
  if hidden_count > 0 then
    table.insert(items, {
      text = "（已隐藏 " .. hidden_count .. " 条原文中查无此名的规则）",
      separator = true,
    })
  end
  -- 极端情况：全部规则都是空头 → order 为空，给一条明确提示而非空白列表
  if #order == 0 then
    table.insert(items, {
      text = "（本书暂无可用别名：现有规则在原文中均查无此名）",
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
    -- preFix31（2026-09-29）：按用户指示移除 preFix29 加回的「重新应用替换（重载本书）」
    -- 菜单项。应用入口仍保留两条既有通路：①采纳规则保存后的应用弹窗
    -- （offerApplyAfterRuleChange）；②改名/停用规则保存即应用。
    -- applyAndReload 函数本体保留（弹窗链路仍在调用），0 条规则护栏也在函数内。
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
