-- KOAI mention_scan.lua（v2.0 新增，v2.0.10 修复统一检索）
-- 人物全文提及：参照社区 XRAY 插件的 Mention Scanning 思路，
-- 纯本地扫描全书文本，找出某个人物名出现的页码与上下文片段，点击跳转。
--  · 不调 AI、不耗 token；结果按书缓存（书文件变化自动失效），第二次秒开；
--  · 扫描用 crengine C 层搜索 findAllText，页码由 item.start(XPointer)
--    经 getPageFromXPointer 换算（v2.0.10 修复：旧代码读 item.page 恒为 nil）；
--  · v2.0.10：按人物合并组统一检索——昵称与全部原名叫法一起查，结果按页合并；
--  · 跳转用 GotoPage 事件，跳转前压入位置栈（ReaderLink），可返回原位置。
--  · 与人名替换的关系（v2.7.5 自适应）：
--    - 替换已生效（规则启用、非待生效、且在 applyAndReload 写入的生效签名里）
--      → 书里已全是昵称，只检索昵称本身（N 次全书检索变 1 次，大书明显提速）；
--    - 未生效/暂停/签名对不上 → 保持检索合并组全部叫法（老叫法仍在书中）；
--    - 兜底：昵称检索 0 命中时自动回退全量叫法检索，宁可慢也不漏。

local lfs = require("libs/libkoreader-lfs")
local logger = require("logger")
local md5 = require("ffi/sha2").md5
local DataStorage = require("datastorage")
local Event = require("ui/event")
local UIManager = require("ui/uimanager")
local InfoMessage = require("ui/widget/infomessage")
local ConfirmBox = require("ui/widget/confirmbox")
local ButtonDialog = require("ui/widget/buttondialog")
local Utils = require("utils")
local json = require("json")
local _ = require("gettext")

local MentionScan = {}

local cache_dir = DataStorage:getDataDir() .. "/koai_name_cache/mentions_v2"
local MAX_RESULTS = 200   -- 每个人物全书最多记录的提及数
local MAX_SHOW = 30       -- 结果列表一次最多显示的行数

-- ============ 基础工具 ============

local function trim(s)
  if type(s) ~= "string" then return "" end
  return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

local function ensureDir(path)
  if lfs.attributes(path, "mode") ~= "directory" then
    lfs.mkdir(path)
  end
end

-- 缓存键 = 文件路径 + 大小 + 修改时间（替换生效后书文件变化，缓存自动失效）
local function cachePath(ui)
  if not (ui and ui.document) then return nil end
  local file = ui.document.file
  if not file then return nil end
  local attr = lfs.attributes(file)
  if not attr then return nil end
  local key = file .. "|" .. tostring(attr.size or 0) .. "|" .. tostring(attr.modification or 0)
  ensureDir(cache_dir)
  return cache_dir .. "/" .. md5(key):sub(1, 16) .. ".json"
end

local function loadCache(ui)
  local p = cachePath(ui)
  if not p then return {} end
  local f = io.open(p, "r")
  if not f then return {} end
  local content = f:read("*all")
  f:close()
  local ok, data = pcall(json.decode, content)
  if ok and type(data) == "table" then return data end
  return {}
end

local function saveCache(ui, data)
  local p = cachePath(ui)
  if not p then return end
  local ok, enc = pcall(json.encode, data)
  if not ok or not enc then return end
  local f = io.open(p, "w")
  if not f then return end
  f:write(enc)
  f:close()
end

-- ============ 候选人物（纯本地收集；合并组统一检索） ============

-- 前置声明（collectPersons 内部调用，定义在其后）
local mergePersons

-- 返回 persons = { { display="阿辽沙", variants={"阿辽沙","阿列克塞·费奥多罗维奇",...} }, ... }
local function collectPersons(ui)
  local persons = {}
  local used = {}   -- 已被分组收编的叫法，避免再出现同名散项
  -- 来源1：人物别名规则，按昵称分组（昵称 + 该人物全部原名叫法一起查）
  pcall(function()
    local NameReplace = require("name_replace")
    if NameReplace.getPersonGroups then
      NameReplace.getPersonGroups(ui, function(g)
        local display = trim(tostring(g and g.nick or ""))
        if display == "" then return end
        local variants = { display }
        local seen = { [display] = true }
        for _, o in ipairs(g.originals or {}) do
          o = trim(tostring(o or ""))
          if o ~= "" and not seen[o] then
            seen[o] = true
            variants[#variants + 1] = o
          end
        end
        persons[#persons + 1] = {
          display = display,
          variants = variants,
          -- v2.7.5：规则组附带替换生效状态（name_replace.getPersonGroups 计算）
          applied = g.applied and true or false,
        }
        for _, v in ipairs(variants) do used[v] = true end
      end)
    end
  end)
  -- 来源2：人物卡（卡名 + 卡片别名算同一个人的叫法）
  pcall(function()
    local Storage = require("companion_storage")
    local book = Storage.getBookInfo(ui)
    local cards = Storage.loadCards(book)
    for _, c in ipairs(cards.items or {}) do
      if type(c) == "table" and trim(tostring(c.name or "")) ~= "" then
        local name = trim(tostring(c.name))
        if not used[name] then
          local variants = { name }
          local seen = { [name] = true }
          if type(c.aliases) == "table" then
            for _, a in ipairs(c.aliases) do
              a = trim(tostring(a or ""))
              if a ~= "" and not seen[a] then
                seen[a] = true
                variants[#variants + 1] = a
              end
            end
          end
          persons[#persons + 1] = { display = name, variants = variants, applied = false }
          for _, v in ipairs(variants) do used[v] = true end
        end
      end
    end
  end)
  return mergePersons(persons)
end

-- v2.0.11：跨来源合并——人物卡与别名规则可能描述同一个人（如卡片名
-- 「卡拉马佐夫家的第三个儿子（"卡老三"）」的别名里有"卡老三"，与规则组
-- 昵称相同）。凡共享任一叫法的条目归并为一人；显示名优先取先收集的
-- 规则昵称（规则来源排在卡片来源之前），与书内实际替换结果一致。
mergePersons = function(persons)
  if #persons <= 1 then
    if persons[1] then persons[1].applied = persons[1].applied and true or false end
    return persons
  end
  local parent = {}
  for i = 1, #persons do parent[i] = i end
  local function find(x)
    while parent[x] ~= x do
      parent[x] = parent[parent[x]]
      x = parent[x]
    end
    return x
  end
  local owner = {}   -- 叫法 -> 首次出现的条目号（并查集连通）
  for i, p in ipairs(persons) do
    for _, v in ipairs(p.variants) do
      if owner[v] then
        local a, b = find(owner[v]), find(i)
        if a ~= b then parent[b] = a end
      else
        owner[v] = i
      end
    end
  end
  local merged, order = {}, {}
  for i, p in ipairs(persons) do
    local root = find(i)
    if not merged[root] then
      merged[root] = {
        display = p.display, variants = {}, seen = {},
        applied = p.applied and true or false,
      }
      order[#order + 1] = root
    end
    local m = merged[root]
    -- v2.7.5：合并组只要任一来源的替换已生效，正文里就是昵称态
    m.applied = m.applied or (p.applied and true or false)
    local function push(v)
      v = trim(tostring(v or ""))
      if v ~= "" and #v <= 50 and not m.seen[v] then
        m.seen[v] = true
        m.variants[#m.variants + 1] = v
      end
    end
    push(p.display)
    for _, v in ipairs(p.variants) do push(v) end
  end
  local out = {}
  for _, root in ipairs(order) do
    out[#out + 1] = merged[root]
  end
  return out
end

-- ============ 全书扫描（crengine C 层搜索，按人物全部叫法统一检索） ============

local function scanBook(ui, variants)
  local doc = ui.document
  -- v2.0.7：改用 crengine C 层全文搜索 findAllText（页码可靠，不经 UnicodeToLocal）。
  -- 原逐页取文方案两层实锤不可行（2026-09-25 真机）：
  --   ①单点 getTextFromXPointer(页书签) 静默返回 nil；
  --   ②区间取文虽有返回，但 cre.cpp 对所有取文接口的返回文本一律走
  --     UnicodeToLocal——全部汉字被硬编码替换成 '?'，永远搜不到中文。
  if not (doc and doc.findAllText) then
    return nil, "当前文档不支持全文搜索（仅支持 EPUB 等 CRE 文档）。"
  end
  -- v2.0.10 修复（2026-09-26 真机）：
  --   ①返回项没有 page 字段！页码必须由 item.start（XPointer）经
  --     getPageFromXPointer 换算（readersearch.lua:738 同款做法），
  --     之前读 item.page 恒为 nil → 所有结果被丢 → 误报"全书没有找到"。
  --   ②按人物合并组的全部叫法逐一检索，结果按页合并去重。
  local results = {}
  local page_index = {}
  for _, name in ipairs(variants) do
    local ok, res = pcall(function()
      return doc:findAllText(name, true, 3, 200, false, 0)
    end)
    if ok and type(res) == "table" then
      for _, item in ipairs(res) do
        local page
        pcall(function()
          local xp = item and item.start
          if xp and doc.getPageFromXPointer then
            page = tonumber(doc:getPageFromXPointer(xp))
          end
        end)
        if not page then page = tonumber(item and item.page) end -- 兼容旧结构
        if page and page > 0 then
          local idx = page_index[page]
          if not idx then
            idx = #results + 1
            page_index[page] = idx
            -- v2.0.10b：matched 必须是纯数组（JSON 落盘不失真）；
            -- 去重 set 独立存一份（matched_set），两者绝不能混在一张表里——
            -- 混合表经 JSON 编码会变成纯 map，读回后 #matched==0，
            -- 曾导致 showResults 拼接 nil 崩溃（crash.log 233 行实锤）。
            results[idx] = { page = page, snippet = nil, matched = {}, matched_set = {} }
          end
          local rec = results[idx]
          if not rec.matched_set[name] then
            rec.matched_set[name] = true
            rec.matched[#rec.matched + 1] = name
          end
          -- 摘要：cre 上下文可能也是 '?' 垃圾（同一转换缺陷），仅在其含 CJK 时使用
          if not rec.snippet then
            local prev = tostring(item and item.prev_text or "")
            local next_t = tostring(item and item.next_text or "")
            if prev:match("[\228-\233]") or next_t:match("[\228-\233]") then
              rec.snippet = trim((prev .. name .. next_t):gsub("%s+", " "))
            end
          end
        end
        if #results >= MAX_RESULTS then break end
      end
    end
    if #results >= MAX_RESULTS then break end
  end
  table.sort(results, function(a, b) return a.page < b.page end)
  -- 没取到上下文时兜底用命中的叫法本身
  for _, r in ipairs(results) do
    if not r.snippet then
      r.snippet = r.matched[#r.matched] or ""
    end
  end
  return results, nil
end

-- ============ 结果展示与跳转 ============

local function jumpToPage(ui, page)
  pcall(function()
    if ui.link and ui.link.addCurrentLocationToStack then
      ui.link:addCurrentLocationToStack()
    end
    ui:handleEvent(Event:new("GotoPage", page))
  end)
end

local function showResults(ui, person, mentions, start_idx)
  if #mentions == 0 then
    UIManager:show(InfoMessage:new {
    text = "全书没有找到「" .. person.display .. "」。\n"
        .. (person.applied
            and ("（已检索「" .. person.display .. "」，0 命中后又回退检索了它的全部 "
                .. #person.variants .. " 个叫法）")
            or ("（已同时检索它的全部叫法：共 " .. #person.variants .. " 个）")),
      timeout = 7,
    })
    return
  end
  -- v2.0.10c：分页浏览（用户确认方案）——每页 MAX_SHOW 行，底部上一页/下一页翻页，
  -- 全部结果可翻到，不再只显示前 30 处。
  local dialog
  local total = #mentions
  start_idx = math.max(1, tonumber(start_idx) or 1)
  if start_idx > total then start_idx = 1 end
  local page_no = math.floor((start_idx - 1) / MAX_SHOW) + 1
  local page_total = math.ceil(total / MAX_SHOW)
  local end_idx = math.min(total, start_idx + MAX_SHOW - 1)

  local buttons = {}
  for i = start_idx, end_idx do
    local m = mentions[i]
    -- 防御：matched 可能来自旧缓存（结构异常），取不到就叫法名兜底
    local ml = type(m.matched) == "table" and m.matched or {}
    local first = ml[1] or person.variants[1] or person.display
    local prefix = ""
    if #ml > 1 then
      prefix = "〔" .. table.concat(ml, " ") .. "〕"
    elseif #person.variants > 1 and not person.applied then
      -- v2.7.5：替换已生效时全文只会命中昵称一种叫法，不再加前缀去噪
      prefix = "〔" .. tostring(first) .. "〕"
    end
    buttons[#buttons + 1] = {{
      text = "第 " .. m.page .. " 页｜" .. prefix .. Utils.utf8Truncate(tostring(m.snippet or ""), 40, "……"),
      callback = function()
        UIManager:close(dialog)
        jumpToPage(ui, m.page)
      end,
    }}
  end
  -- 翻页行（仅一页时不显示）
  if page_total > 1 then
    local nav = {}
    if page_no > 1 then
      nav[#nav + 1] = {
        text = "◂ 上一页",
        callback = function()
          UIManager:close(dialog)
          local ok, err = pcall(showResults, ui, person, mentions, start_idx - MAX_SHOW)
          if not ok then logger.err("KOAI MentionScan: page nav failed: ", err) end
        end,
      }
    end
    if page_no < page_total then
      nav[#nav + 1] = {
        text = "下一页 ▸",
        callback = function()
          UIManager:close(dialog)
          local ok, err = pcall(showResults, ui, person, mentions, start_idx + MAX_SHOW)
          if not ok then logger.err("KOAI MentionScan: page nav failed: ", err) end
        end,
      }
    end
    buttons[#buttons + 1] = nav
  end
  buttons[#buttons + 1] = {{
    text = _("关闭"),
    callback = function()
      UIManager:close(dialog)
    end,
  }}
  local title = "「" .. person.display .. "」全文提及（共 " .. total .. " 处）"
  if page_total > 1 then
    title = title .. "  第 " .. page_no .. "/" .. page_total .. " 页"
  end
  dialog = ButtonDialog:new {
    title = title,
    title_align = "center",
    buttons = buttons,
  }
  UIManager:show(dialog)
end

local function variantsHash(variants)
  return table.concat(variants, "\1")
end

-- v2.7.5：缓存键加入替换生效状态——应用替换会改写书文件（缓存自动失效），
-- 但"暂停未应用""加规则未应用"等状态变化不动文件，必须靠键区分，
-- 否则会拿到生效状态不同期的旧扫描结果
local function cacheHash(person)
  return variantsHash(person.variants) .. "|" .. (person.applied and "A" or "F")
end

function MentionScan.showMentionsFor(ui, person)
  if not (ui and ui.document) then return end
  local cache = loadCache(ui)
  local entry = cache[person.display]
  if type(entry) == "table"
      and type(entry.mentions) == "table"
      and entry.vhash == cacheHash(person) then
    -- 展示层任何异常都不允许带崩 KOReader（v2.0.10b）
    local ok, err = pcall(showResults, ui, person, entry.mentions)
    if not ok then logger.err("KOAI MentionScan: showResults failed: ", err) end
    return
  end
  UIManager:show(ConfirmBox:new {
    text = "还没有「" .. person.display .. "」的扫描结果。\n"
        .. (person.applied
            and ("替换已生效，将直接检索「" .. person.display .. "」"
                .. (#person.variants > 1
                    and ("（免查其余 " .. (#person.variants - 1)
                        .. " 个老叫法，扫描更快；0 命中会自动回退全量检索）") or "")
                .. "\n\n")
            or (person.variants and #person.variants > 1
                and ("将同时检索它的 " .. #person.variants .. " 个叫法：\n"
                    .. table.concat(person.variants, "、") .. "\n\n")
                or ""))
        .. "现在扫描全书吗？（纯本地不耗 token，大书约几秒，结果会缓存）",
    ok_text = "扫描",
    cancel_text = "取消",
    ok_callback = function()
      local loading = InfoMessage:new {
        text = "正在扫描全书……",
        timeout = nil,
      }
      UIManager:show(loading)
      UIManager:scheduleIn(0.1, function()
        -- v2.7.5：替换已生效 → 只检索昵称（老叫法已不在书文件里）；
        -- 0 命中时回退全量叫法检索兜底（生效状态异常时宁可慢也不漏）
        local search_names = person.variants
        if person.applied then search_names = { person.display } end
        local ok, results, err = pcall(scanBook, ui, search_names)
        if not ok then
          err = results
          results = nil
        end
        if results and #results == 0 and #search_names < #person.variants then
          logger.info("KOAI MentionScan: nickname-only scan empty, fallback to all variants")
          local ok2, results2, err2 = pcall(scanBook, ui, person.variants)
          if ok2 then
            results = results2
          else
            logger.warn("KOAI MentionScan: fallback scan failed: ", tostring(err2))
          end
        end
        UIManager:close(loading)
        if not results then
          UIManager:show(InfoMessage:new {
            text = "扫描失败：\n" .. tostring(err or "未知错误"),
            timeout = 7,
          })
          return
        end
        cache[person.display] = { vhash = cacheHash(person), mentions = results }
        saveCache(ui, cache)
        local ok_r, err_r = pcall(showResults, ui, person, results)
        if not ok_r then logger.err("KOAI MentionScan: showResults failed: ", err_r) end
      end)
    end,
  })
end

-- ============ 入口：选人 → 扫描/缓存 → 结果 → 跳转 ============

function MentionScan.show(ui)
  if not (ui and ui.document) then return end
  local persons = collectPersons(ui)
  if #persons == 0 then
    UIManager:show(InfoMessage:new {
      text = "还没有可选的人物名。\n"
          .. "可在\"人物别名\"里添加别名，或在精读模式建立人物卡后再来。",
      timeout = 7,
    })
    return
  end

  local dialog
  local buttons = {}
  local row = {}
  for i, p in ipairs(persons) do
    row[#row + 1] = {
      text = p.display .. (#p.variants > 1 and ("（" .. #p.variants .. " 个叫法）") or ""),
      callback = function()
        UIManager:close(dialog)
        UIManager:nextTick(function()
          MentionScan.showMentionsFor(ui, p)
        end)
      end,
    }
    if #row == 2 or i == #persons then
      buttons[#buttons + 1] = row
      row = {}
    end
  end
  buttons[#buttons + 1] = {{
    text = _("关闭"),
    callback = function()
      UIManager:close(dialog)
    end,
  }}
  dialog = ButtonDialog:new {
    title = "人物全文提及：选择要查找的人物",
    title_align = "center",
    buttons = buttons,
  }
  UIManager:show(dialog)
end

return MentionScan
