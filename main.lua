--==========================================================================
--  lolcat  |  Matcha edition  |  Rivals
--
--  Written for the Matcha LuaVM (external, no hooks, no remotes):
--    * UI            : Drawing API, rebuilt with lolcat's palette / metrics
--    * Ragebot       : Evasion Off / Random / Translocate  (no desync, no FireServer)
--                      moves your HumanoidRootPart, aims with mousemoverel,
--                      fires with mouse1click
--    * Everything else uses only documented Matcha APIs.
--
--  Memory features (Gravity, camera look vector) need
--  "allow unsafe LuaU execution" and the offsets in OFF below. Everything
--  checks the pointers first and fails soft, and Settings > General has a
--  "Copy Diagnostics" button that reports what works on your build.
--==========================================================================

local G = _G
if not pcall(function() G.__lolcat_probe = true end) then G = {} end
if G.lolcatMatcha and G.lolcatMatcha.Unload then pcall(G.lolcatMatcha.Unload) end
local K = { alive = true, errors = {}, errorCount = 0 }
G.lolcatMatcha = K

--------------------------------------------------------------------------
-- services & locals
--------------------------------------------------------------------------
local Players = game:GetService("Players")
local HttpService = game:GetService("HttpService")
local LocalPlayer = Players.LocalPlayer
local Mouse = LocalPlayer:GetMouse()

local floor, ceil, max, min, abs, sqrt, sin, cos, pi, random =
    math.floor, math.ceil, math.max, math.min, math.abs, math.sqrt, math.sin, math.cos, math.pi, math.random
local fmt = string.format
local insert, remove, sort = table.insert, table.remove, table.sort

local function clamp(v, a, b) if v < a then return a end if v > b then return b end return v end
local function lerp(a, b, t) return a + (b - a) * t end
local function round(v) return floor(v + 0.5) end
local function try(f, ...) local ok, a = pcall(f, ...) if ok then return a end return nil end

local hasMem = type(memory_read) == "function" and type(memory_write) == "function"

-- imtheo offsets (offsets.imtheo.lol). Edit here when Roblox updates.
local OFF = {
    WorkspaceToWorld = 0x400,
    WorldGravity     = 0x22C,
    CameraRotation   = 0xC8,
}

--------------------------------------------------------------------------
-- colours  (packed 0xRRGGBB integers so they compare cheaply)
--------------------------------------------------------------------------
local function pack(r, g, b) return floor(r) * 65536 + floor(g) * 256 + floor(b) end
local function rgb3(c) return floor(c / 65536) % 256, floor(c / 256) % 256, c % 256 end
local function mix(a, b, t)
    local ar, ag, ab = rgb3(a)
    local br, bg, bb = rgb3(b)
    return pack(lerp(ar, br, t) + 0.5, lerp(ag, bg, t) + 0.5, lerp(ab, bb, t) + 0.5)
end

-- lolcat's own theme table (Theme defaults in the dump)
local T = {
    Accent = pack(154, 213, 222), Outline = pack(24, 25, 24), Background = pack(0, 0, 0),
    ElementBackground = pack(6, 6, 6), TabButtonSelected = pack(51, 65, 70), Unselected = pack(75, 72, 72),
    TextColor = pack(197, 197, 197), ToggleCircleUnselected = pack(70, 85, 87),
    ToggleBackgroundUnselected = pack(12, 13, 13), GradientTop = pack(14, 16, 16), GradientMid = pack(6, 6, 6),
    GradientDark = pack(3, 3, 3), TabHighlight = pack(51, 65, 70), TabShadow = pack(30, 51, 61),
    White = pack(255, 255, 255),
}

local function hsv2c(h, s, v)
    h = (h % 1) * 6
    local i = floor(h)
    local f = h - i
    local p, q, t = v * (1 - s), v * (1 - s * f), v * (1 - s * (1 - f))
    local r, g, b
    i = i % 6
    if i == 0 then r, g, b = v, t, p elseif i == 1 then r, g, b = q, v, p elseif i == 2 then r, g, b = p, v, t
    elseif i == 3 then r, g, b = p, q, v elseif i == 4 then r, g, b = t, p, v else r, g, b = v, p, q end
    return pack(r * 255 + 0.5, g * 255 + 0.5, b * 255 + 0.5)
end
local function c2hsv(c)
    local r, g, b = rgb3(c)
    r, g, b = r / 255, g / 255, b / 255
    local mx, mn = max(r, g, b), min(r, g, b)
    local d = mx - mn
    local h = 0
    if d > 0 then
        if mx == r then h = ((g - b) / d) % 6 elseif mx == g then h = (b - r) / d + 2 else h = (r - g) / d + 4 end
        h = h / 6
    end
    local s = 0
    if mx > 0 then s = d / mx end
    return h, s, mx
end

--------------------------------------------------------------------------
-- renderer: pooled Drawing objects with per-property change cache
--------------------------------------------------------------------------
local R = { clip = nil }
local KINDS = { "Square", "Text", "Line", "Circle" }
local pool, used, shown = {}, {}, {}
for _, k in ipairs(KINDS) do pool[k] = {}; used[k] = 0; shown[k] = 0 end
local zc = 0
local colorMemo = {}
local FONT, FONT_BOLD = nil, nil
do
    local f = try(function() return Drawing.Fonts end)
    if f then
        FONT = f.System or f.UI
        FONT_BOLD = f.SystemBold or FONT
    end
end

local function C3(p)
    local c = colorMemo[p]
    if not c then
        local r, g, b = rgb3(p)
        c = Color3.fromRGB(r, g, b)
        colorMemo[p] = c
    end
    return c
end

-- Matcha rejects some documented property names ("Unknown property FontSize"),
-- so every write is protected; a property that throws once is disabled for good
-- and listed in the diagnostics instead of aborting the whole frame.
local badProps = {}
K.badProps = badProps
local function put(o, k, v)
    if badProps[k] then return false end
    local ok, err = pcall(function() o[k] = v end)
    if not ok then
        badProps[k] = tostring(err)
        return false
    end
    return true
end

-- Text size property: the docs say FontSize, the runtime may want Size/TextSize.
local TEXT_SIZE = "FontSize"
do
    local t = try(function() return Drawing.new("Text") end)
    if t then
        local found
        for _, cand in ipairs({ "FontSize", "Size", "TextSize" }) do
            if not found and pcall(function() t[cand] = 13 end) then found = cand end
        end
        if not found then
            for _, cand in ipairs({ "Size", "FontSize" }) do
                if not found and pcall(function() t[cand] = Vector2.new(13, 13) end) then found = cand end
            end
        end
        if found then TEXT_SIZE = found end
        K.textSizeProp = found or "none"
        pcall(function() t:Remove() end)
    end
end

local function acquire(kind)
    local u = used[kind] + 1
    used[kind] = u
    local e = pool[kind][u]
    if not e then
        e = { o = Drawing.new(kind), c = {} }
        pool[kind][u] = e
    end
    zc = zc + 1
    local c = e.c
    if c.Visible ~= true then c.Visible = true; put(e.o, "Visible", true) end
    if c.ZIndex ~= zc then c.ZIndex = zc; put(e.o, "ZIndex", zc) end
    return e
end

local function sp(e, k, v)
    local c = e.c
    if c[k] ~= v then c[k] = v; put(e.o, k, v) end
end
local function setPair(e, prop, kx, ky, x, y)
    local c = e.c
    if c[kx] ~= x or c[ky] ~= y then
        c[kx] = x; c[ky] = y
        put(e.o, prop, Vector2.new(x, y))
    end
end
local function setCorner(e, r)
    if e.c.Corner ~= r then
        e.c.Corner = r
        put(e.o, "Corner", r)
    end
end

function R.tw(s, size) return #s * size * 0.52 end

function R.rect(x, y, w, h, color, corner, alpha)
    local cl = R.clip
    if cl then
        local x2, y2 = x + w, y + h
        if x < cl[1] then x = cl[1] end
        if y < cl[2] then y = cl[2] end
        if x2 > cl[3] then x2 = cl[3] end
        if y2 > cl[4] then y2 = cl[4] end
        w, h = x2 - x, y2 - y
    end
    if w < 1 or h < 1 then return end
    local e = acquire("Square")
    setPair(e, "Position", "px", "py", round(x), round(y))
    setPair(e, "Size", "sx", "sy", round(w), round(h))
    sp(e, "Filled", true)
    sp(e, "Color", C3(color))
    sp(e, "Transparency", alpha or 1)
    setCorner(e, corner or 0)
end

function R.border(x, y, w, h, color, th)
    th = th or 1
    R.rect(x, y, w, th, color)
    R.rect(x, y + h - th, w, th, color)
    R.rect(x, y + th, th, h - th * 2, color)
    R.rect(x + w - th, y + th, th, h - th * 2, color)
end

function R.vgrad(x, y, w, h, c1, c2, steps)
    local sh = h / steps
    for i = 0, steps - 1 do
        local t = 0
        if steps > 1 then t = i / (steps - 1) end
        R.rect(x, y + floor(i * sh), w, ceil(sh) + 1, mix(c1, c2, t))
    end
end

function R.text(x, y, s, size, color, bold, outline)
    local cl = R.clip
    if cl and (y < cl[2] or y + size + 2 > cl[4] or x < cl[1] or x > cl[3]) then return end
    local e = acquire("Text")
    setPair(e, "Position", "px", "py", round(x), round(y))
    sp(e, "Text", s)
    sp(e, TEXT_SIZE, size)
    sp(e, "Color", C3(color))
    local f = FONT
    if bold then f = FONT_BOLD end
    if f then sp(e, "Font", f) end
    sp(e, "Outline", outline == true)
    sp(e, "Center", false)
end

function R.line(x1, y1, x2, y2, color, th)
    local e = acquire("Line")
    setPair(e, "From", "fx", "fy", round(x1), round(y1))
    setPair(e, "To", "tx", "ty", round(x2), round(y2))
    sp(e, "Thickness", th or 1)
    sp(e, "Color", C3(color))
end

function R.circle(cx, cy, r, color, filled, th, sides)
    local cl = R.clip
    if cl and (cx - r < cl[1] or cx + r > cl[3] or cy - r < cl[2] or cy + r > cl[4]) then return end
    local e = acquire("Circle")
    setPair(e, "Position", "px", "py", round(cx), round(cy))
    sp(e, "Radius", r)
    sp(e, "NumSides", sides or 32)
    sp(e, "Thickness", th or 1)
    sp(e, "Filled", filled == true)
    sp(e, "Color", C3(color))
end

-- Pictures (Drawing "Image"): one object per key, kept between frames so a texture is
-- uploaded once. Images can't be clipped, so one is only drawn if it fits inside R.clip.
local imgPool, imgDrawn, imgSeen, imgCount = {}, {}, {}, 0
function R.image(path, data, x, y, w, h)
    local cl = R.clip
    if cl and (x < cl[1] or y < cl[2] or x + w > cl[3] or y + h > cl[4]) then return false end
    local n = (imgSeen[path] or 0) + 1
    imgSeen[path] = n
    local key = path .. "#" .. n
    local e = imgPool[key]
    if not e then
        local o = try(function() return Drawing.new("Image") end)
        if not o then return false end
        e = { o = o, c = {} }
        imgPool[key] = e
        imgCount = imgCount + 1
    end
    if e.c.Data ~= data then e.c.Data = data; put(e.o, "Data", data) end
    zc = zc + 1
    sp(e, "ZIndex", zc)
    setPair(e, "Position", "px", "py", round(x), round(y))
    setPair(e, "Size", "sx", "sy", round(w), round(h))
    sp(e, "Transparency", 1)
    sp(e, "Visible", true)
    imgDrawn[key] = true
    return true
end

function R.flush()
    for key, e in pairs(imgPool) do
        if not imgDrawn[key] and e.c.Visible ~= false then sp(e, "Visible", false) end
    end
    if imgCount > 160 then
        for key, e in pairs(imgPool) do
            if not imgDrawn[key] and imgCount > 120 then
                pcall(function() e.o:Remove() end)
                imgPool[key] = nil
                imgCount = imgCount - 1
            end
        end
    end
    imgDrawn, imgSeen = {}, {}
    for _, k in ipairs(KINDS) do
        local u, p = used[k], pool[k]
        for i = u + 1, shown[k] do
            local e = p[i]
            if e then sp(e, "Visible", false) end
        end
        shown[k] = u
        used[k] = 0
    end
    zc = 0
end

function R.destroy()
    for _, e in pairs(imgPool) do pcall(function() e.o.Visible = false; e.o:Remove() end) end
    imgPool, imgDrawn, imgSeen, imgCount = {}, {}, {}, 0
    for _, k in ipairs(KINDS) do
        for _, e in ipairs(pool[k]) do pcall(function() e.o:Remove() end) end
        pool[k] = {}
        used[k] = 0
        shown[k] = 0
    end
end

--------------------------------------------------------------------------
-- input
--------------------------------------------------------------------------
local I = { mx = 0, my = 0, down = false, pressed = false, rdown = false, rpressed = false }
local function keyDown(vk)
    if not vk then return false end
    return iskeypressed(vk) and true or false
end

local KeyNames = {
    [0x01] = "LMB", [0x02] = "RMB", [0x04] = "MMB", [0x05] = "MB4", [0x06] = "MB5", [0x08] = "Back",
    [0x09] = "Tab", [0x0D] = "Enter", [0x10] = "Shift", [0x11] = "Ctrl", [0x12] = "Alt", [0x14] = "Caps",
    [0x20] = "Space", [0x21] = "PgUp", [0x22] = "PgDn", [0x23] = "End", [0x24] = "Home", [0x25] = "Left",
    [0x26] = "Up", [0x27] = "Right", [0x28] = "Down", [0x2D] = "Ins", [0x2E] = "Del",
    [0xA0] = "LShift", [0xA1] = "RShift", [0xA2] = "LCtrl", [0xA3] = "RCtrl", [0xA4] = "LAlt", [0xA5] = "RAlt",
}
for i = 0x30, 0x39 do KeyNames[i] = string.char(i) end
for i = 0x41, 0x5A do KeyNames[i] = string.char(i) end
for i = 0, 9 do KeyNames[0x60 + i] = "Num" .. i end
for i = 1, 12 do KeyNames[0x6F + i] = "F" .. i end
local function keyName(vk) if not vk then return "None" end return KeyNames[vk] or fmt("0x%X", vk) end

function I.update()
    pcall(function()
        I.mx = Mouse.X
        I.my = Mouse.Y + (K.cfg and K.cfg.Menu.yOffset or 0)
    end)
    local d = ismouse1pressed() and true or false
    I.pressed = d and not I.down
    I.down = d
    local r = ismouse2pressed() and true or false
    I.rpressed = r and not I.rdown
    I.rdown = r
end
function I.inside(x, y, w, h) return I.mx >= x and I.mx <= x + w and I.my >= y and I.my <= y + h end

--------------------------------------------------------------------------
-- keybinds (Always / Toggle / Hold, same as lolcat's keybind widget)
--------------------------------------------------------------------------
local allBinds = {}
local function Bind(kind, key, name)
    local b = { _isBind = true, kind = kind, key = key, state = false, prev = false, active = false, name = name }
    insert(allBinds, b)
    return b
end
local function evalBind(b)
    if b.kind == "Always" then b.active = true return end
    local d = keyDown(b.key)
    if b.kind == "Hold" then b.active = d return end
    if d and not b.prev then b.state = not b.state end
    b.prev = d
    b.active = b.state
end
local function featureOn(cfg) return cfg.enabled and cfg.bind.active end

--------------------------------------------------------------------------
-- settings store (defaults mirror lolcat's Ragebot / Aimbot / ESP layout)
--------------------------------------------------------------------------
local function espSide(on)
    return {
        enabled = on,
        name = { on = true, color = pack(255, 255, 255) },
        box = { on = true, style = "Full", color = T.Accent },
        health = { on = true },
        healthNum = { on = false, color = pack(255, 255, 255) },
        distance = { on = true, color = pack(200, 200, 200) },
        tracer = { on = false, origin = "Bottom", color = T.Accent },
        head = { on = false, color = pack(255, 80, 80) },
        skeleton = { on = false, color = pack(255, 255, 255) },
    }
end

local Cfg = {
    Aimbot = {
        enabled = false, bind = Bind("Hold", 0x02, "Aimbot"), teamCheck = true, part = "Head", smooth = 10,
        maxDist = 1500, fov = 150, showFov = true, fovColor = T.Accent, origin = "Center",
        predict = false, predictMs = 60,
    },
    Ragebot = {
        enabled = false, bind = Bind("Always", nil, "Ragebot"), teamCheck = true, priority = "Closest",
        maxDist = 2500, shootFrames = 2, autoFire = true, equip = "Off",
        glue = { dist = 8 },
        evasion = { mode = "Random", evadeFrames = 1, anchor = "Target", radius = 60, factor = 0.5, yRange = 15 },
    },
    Trigger = { enabled = false, bind = Bind("Always", nil, "Triggerbot"), radius = 14, delay = 40, cooldown = 120, teamCheck = true },
    Esp = {
        enabled = true, bind = Bind("Always", nil, "ESP"), maxDist = 1500, textSize = 13,
        Enemy = espSide(true), Team = espSide(false),
    },
    Crosshair = { enabled = false, size = 8, gap = 4, thick = 2, color = pack(255, 255, 255), dot = false },
    Movement = {
        fly = { enabled = false, bind = Bind("Toggle", 0x56, "Fly"), mode = "Velocity", speed = 60 },
        speed = { enabled = false, bind = Bind("Always", nil, "Speed"), value = 40 },
        noclip = { enabled = false, bind = Bind("Toggle", nil, "Noclip") },
        jump = { enabled = false, bind = Bind("Always", nil, "Infinite Jump"), power = 60 },
    },
    World = {
        light = { enabled = false, timeOn = false, time = 12, brightOn = false, bright = 2, expOn = false, exposure = 0,
            ambOn = false, amb = pack(120, 120, 150), outOn = false, out = pack(140, 140, 170),
            shiftOn = false, shift = pack(255, 200, 150), fogOn = false, fogEnd = 800, fogStart = 0, fog = pack(180, 190, 205) },
        sky = { enabled = false, group = "Cloudy", pick = "cloudy 01" },
        snow = { enabled = false, amount = 160, speed = 1.0, size = 2.5, wind = 0.3, color = pack(255, 255, 255) },
        rain = { enabled = false, amount = 220, speed = 1.0, len = 18, wind = 0.25, color = pack(150, 180, 255), thunder = false },
        tint = { enabled = false, color = pack(80, 120, 255), alpha = 0.25, rainbow = false, rspeed = 0.2 },
        vignette = { enabled = false, alpha = 0.5 },
        dim = { enabled = false, alpha = 0.3 },
    },
    Silent = {
        enabled = false, bind = Bind("Hold", 0x05, "Silent Aim"), teamCheck = true, part = "Head", maxDist = 1500,
        fov = 120, showFov = true, fovColor = T.Accent, delay = 80, autoFire = true, predict = false, predictMs = 60,
    },
    Gun = {
        enabled = false,
        recOn = true, recoil = 0, sprOn = true, spread = 0, accOn = true, accuracy = 0,
        cdOn = true, cooldown = 0, spdOn = true, projSpeed = 5000,
        fullAuto = false, autoDelay = 25,
    },
    Melee = { enabled = false, cd = 0.001, generic = false },
    Menu = { key = 0xA1, panic = 0x23, watermark = true, keylist = true, accent = T.Accent, yOffset = 0, slot = "1", performance = "Ultra" },
}
K.cfg = Cfg
Cfg.Aimbot.bind.owner = Cfg.Aimbot
Cfg.Ragebot.bind.owner = Cfg.Ragebot
Cfg.Trigger.bind.owner = Cfg.Trigger
Cfg.Esp.bind.owner = Cfg.Esp
Cfg.Silent.bind.owner = Cfg.Silent
Cfg.Movement.fly.bind.owner = Cfg.Movement.fly
Cfg.Movement.speed.bind.owner = Cfg.Movement.speed
Cfg.Movement.noclip.bind.owner = Cfg.Movement.noclip
Cfg.Movement.jump.bind.owner = Cfg.Movement.jump

--------------------------------------------------------------------------
-- persistence (writefile / readfile, .json only)
--------------------------------------------------------------------------
local Store = { dir = "lolcatMatcha", msg = "", onLoad = nil }
local function ser(t)
    local o = {}
    for k, v in pairs(t) do
        local tv = type(v)
        if tv == "table" then
            if v._isBind then o[k] = { _isBind = true, kind = v.kind, key = v.key or 0 } else o[k] = ser(v) end
        elseif tv == "number" or tv == "string" or tv == "boolean" then
            o[k] = v
        end
    end
    return o
end
local function deser(dst, src)
    for k, v in pairs(src) do
        local d = dst[k]
        if type(d) == "table" and type(v) == "table" then
            if d._isBind then
                if v.kind == "Hold" or v.kind == "Toggle" or v.kind == "Always" then d.kind = v.kind end
                if type(v.key) == "number" then if v.key > 0 then d.key = v.key else d.key = nil end end
            else
                deser(d, v)
            end
        elseif d ~= nil and type(d) == type(v) then
            dst[k] = v
        end
    end
end
local function slotPath(slot) return Store.dir .. "/configs/slot" .. tostring(slot) .. ".json" end
function Store.save(slot)
    local ok, err = pcall(function()
        makefolder(Store.dir .. "/configs")
        writefile(slotPath(slot), HttpService:JSONEncode(ser(Cfg)))
    end)
    Store.msg = ok and ("Saved slot " .. slot) or ("Save failed: " .. tostring(err))
end
function Store.load(slot)
    local ok, err = pcall(function()
        local p = slotPath(slot)
        assert(isfile(p), "slot is empty")
        deser(Cfg, HttpService:JSONDecode(readfile(p)))
    end)
    Store.msg = ok and ("Loaded slot " .. slot) or ("Load failed: " .. tostring(err))
    if ok and Store.onLoad then pcall(Store.onLoad) end
end
function Store.delete(slot)
    local ok, err = pcall(function() assert(delfile(slotPath(slot)), "slot is empty") end)
    Store.msg = ok and ("Deleted slot " .. slot) or ("Delete failed: " .. tostring(err))
end

--------------------------------------------------------------------------
-- game access
--------------------------------------------------------------------------
local function camera() return workspace.CurrentCamera end
local function viewport()
    local cam = camera()
    local vp = cam and try(function() return cam.ViewportSize end)
    if vp then return vp.X, vp.Y end
    return 1920, 1080
end
local function w2s(v3)
    local p, on = WorldToScreen(v3)
    if on then return p.X, p.Y end
    return nil
end
local function myParts()
    local ch = LocalPlayer.Character
    if not ch then return nil end
    return ch:FindFirstChild("HumanoidRootPart"), ch
end

local Targets = { list = {}, last = 0 }
local function buildEntry(plr)
    local ch = plr.Character
    if not ch then return nil end
    local root = ch:FindFirstChild("HumanoidRootPart")
    local head = ch:FindFirstChild("HitboxHead") or ch:FindFirstChild("Head")
    if not root and not head then return nil end
    local hum = ch:FindFirstChildOfClass("Humanoid") or ch:FindFirstChild("Humanoid")
    local hp, mhp = 100, 100
    if hum then
        hp = hum.Health
        mhp = hum.MaxHealth
        if mhp <= 0 then mhp = 100 end
    end
    local team = try(function() return plr.Team end)
    local mine = try(function() return LocalPlayer.Team end)
    return {
        plr = plr, name = plr.Name, char = ch, root = root or head, head = head, hum = hum,
        hp = hp, maxhp = mhp, alive = hp > 0, enemy = (team == nil) or (team ~= mine),
    }
end
function Targets.refresh()
    local now = tick()
    local pmode = (Cfg.Menu and Cfg.Menu.performance) or "Ultra"
    local rate = pmode == "Ultra" and 0.01 or (pmode == "Middle" and 0.04 or 0.08)
    if now - Targets.last < rate then return end
    Targets.last = now
    local out = {}
    for _, plr in ipairs(Players:GetPlayers()) do
        if plr ~= LocalPlayer then
            local ok, e = pcall(buildEntry, plr)
            if ok and e then out[#out + 1] = e end
        end
    end
    Targets.list = out
end
function Targets.pos(e, part)
    local p = e.head or e.root
    if part == "Torso" then p = e.root end
    return p.Position
end

--------------------------------------------------------------------------
-- camera look vector (memory rotation matrix, self-calibrated through W2S)
--------------------------------------------------------------------------
local Cam = { mode = "none", last = nil, checked = 0, choice = nil }
local function validPtr(p) return type(p) == "number" and p > 0x10000 and p < 0x7FFFFFFFFFFF end
local function readRot(addr)
    local r = {}
    for i = 0, 8 do r[i + 1] = memory_read("float", addr + OFF.CameraRotation + i * 4) end
    return r
end
local function finite(v) return type(v) == "number" and v == v and abs(v) < 1e6 end
function Cam.look()
    local cam = camera()
    if not cam then return Cam.last end
    local camPos = try(function() return cam.Position end)
    local vw, vh = viewport()
    local now = tick()
    if hasMem and camPos and (not Cam.choice or now - Cam.checked > 2) then
        Cam.checked = now
        local addr = try(function() return cam.Address end)
        if validPtr(addr) then
            local r = readRot(addr)
            local ok = true
            for i = 1, 9 do if not finite(r[i]) then ok = false end end
            if ok then
                local cands = {
                    A = Vector3.new(-r[3], -r[6], -r[9]),
                    B = Vector3.new(-r[7], -r[8], -r[9]),
                }
                local best, bestErr
                for name, v in pairs(cands) do
                    if v.Magnitude > 0.5 then
                        local p, on = WorldToScreen(camPos + v.Unit * 20)
                        if on then
                            local err = sqrt((p.X - vw / 2) ^ 2 + (p.Y - vh / 2) ^ 2)
                            if not bestErr or err < bestErr then best, bestErr = name, err end
                        end
                    end
                end
                if best and bestErr < vh * 0.25 then Cam.choice = best else Cam.choice = nil end
            end
        end
    end
    if hasMem and Cam.choice and camPos then
        local addr = try(function() return cam.Address end)
        if validPtr(addr) then
            local r = readRot(addr)
            if finite(r[3]) and finite(r[9]) then
                local v
                if Cam.choice == "A" then v = Vector3.new(-r[3], -r[6], -r[9]) else v = Vector3.new(-r[7], -r[8], -r[9]) end
                if v.Magnitude > 0.5 then
                    Cam.mode = "memory(" .. Cam.choice .. ")"
                    Cam.last = v.Unit
                    return Cam.last
                end
            end
        end
    end
    local root = myParts()
    if root and camPos then
        local d = root.Position - camPos
        if d.Magnitude > 2 then
            Cam.mode = "fallback(root-cam)"
            Cam.last = d.Unit
            return Cam.last
        end
    end
    Cam.mode = "last-known"
    return Cam.last
end

--------------------------------------------------------------------------
-- world (memory): pointer only (fly uses it to zero gravity)
--------------------------------------------------------------------------
local World = { ptr = 0, last = 0, grav0 = nil }
function World.resolve()
    if not hasMem then World.ptr = 0 return end
    local now = tick()
    if World.ptr ~= 0 and now - World.last < 2 then return end
    World.last = now
    local ws = try(function() return workspace.Address end)
    World.ptr = 0
    if validPtr(ws) then
        local w = memory_read("uintptr_t", ws + OFF.WorkspaceToWorld)
        if validPtr(w) then World.ptr = w end
    end
end
function World.get(off)
    if World.ptr == 0 then return nil end
    local v = memory_read("float", World.ptr + off)
    if finite(v) then return v end
    return nil
end
function World.set(off, v)
    if World.ptr == 0 then return false end
    memory_write("float", World.ptr + off, v)
    return true
end
function World.tick()
    World.resolve()
    if World.ptr == 0 then return end
    if World.grav0 and not K.flyGravity then
        World.set(OFF.WorldGravity, World.grav0)
        World.grav0 = nil
    end
end

function World.restore()
    if World.ptr == 0 then return end
    if World.grav0 then World.set(OFF.WorldGravity, World.grav0); World.grav0 = nil end
end

--------------------------------------------------------------------------
-- aim helpers
--------------------------------------------------------------------------
local Aim = { rx = 0, ry = 0 }
function Aim.move(dx, dy)
    Aim.rx = Aim.rx + dx
    Aim.ry = Aim.ry + dy
    local ix, iy = Aim.rx, Aim.ry
    if ix >= 0 then ix = floor(ix) else ix = ceil(ix) end
    if iy >= 0 then iy = floor(iy) else iy = ceil(iy) end
    Aim.rx = Aim.rx - ix
    Aim.ry = Aim.ry - iy
    if ix ~= 0 or iy ~= 0 then mousemoverel(ix, iy) end
end
local function aimOrigin(cfg)
    local vw, vh = viewport()
    if cfg.origin == "Cursor" then return I.mx, I.my end
    return vw / 2, vh / 2
end

function Aim.tick()
    local c = Cfg.Aimbot
    if not featureOn(c) or K.ui.open or not isrbxactive() then return end
    local myRoot = myParts()
    if not myRoot then return end
    local myPos = myRoot.Position
    local ox, oy = aimOrigin(c)
    local best, bx, by, bd = nil, 0, 0, c.fov
    for _, e in ipairs(Targets.list) do
        if e.alive and (not c.teamCheck or e.enemy) then
            local ok, pos = pcall(Targets.pos, e, c.part == "Torso" and "Torso" or "Head")
            if ok then
                local dist = (pos - myPos).Magnitude
                if dist <= c.maxDist then
                    if c.predict then
                        local v = try(function() return e.root.AssemblyLinearVelocity end)
                        if v then pos = pos + v * (c.predictMs / 1000) end
                    end
                    local sx, sy = w2s(pos)
                    if sx then
                        local d = sqrt((sx - ox) ^ 2 + (sy - oy) ^ 2)
                        if d < bd then best, bx, by, bd = e, sx, sy, d end
                    end
                end
            end
        end
    end
    if best then
        local s = max(1, c.smooth)
        local dx, dy = (bx - ox) / s, (by - oy) / s
        local lim = 80
        Aim.move(clamp(dx, -lim, lim), clamp(dy, -lim, lim))
    end
end

local Trig = { last = 0, since = nil }
function Trig.tick()
    local c = Cfg.Trigger
    if not featureOn(c) or K.ui.open or not isrbxactive() then Trig.since = nil return end
    local vw, vh = viewport()
    local hit = false
    for _, e in ipairs(Targets.list) do
        if e.alive and (not c.teamCheck or e.enemy) then
            local ok, pos = pcall(Targets.pos, e, "Head")
            if ok then
                local sx, sy = w2s(pos)
                if sx and sqrt((sx - vw / 2) ^ 2 + (sy - vh / 2) ^ 2) <= c.radius then hit = true break end
            end
        end
    end
    local now = tick()
    if hit then
        if not Trig.since then Trig.since = now end
        if now - Trig.since >= c.delay / 1000 and now - Trig.last >= c.cooldown / 1000 then
            mouse1click()
            Trig.last = now
        end
    else
        Trig.since = nil
    end
end

-- ================= TRANSLOCATE (shared module: identical in UE Helper and lolcat) =================
-- Finds every InstakillOOB part on whatever map is loaded (Workspace.Arena.Barriers first,
-- then Arena, then the whole Workspace); maps without one fall back to plain OOB parts.
-- Snaps you right next to the closest one and orbits the face you are nearest to.  The first position is written instantly (no tween) and sits
-- a hair outside the part (body box + gap) so the kill brick never touches you.
local Translocate_ok, Translocate = pcall(function()
    local M = { list = {}, status = "idle", scanning = false, sig = nil, scanT = -100,
        sel = nil, key = nil, ang = 0, pickT = 99, cu = 0, cv = 0 }
    local abs, sqrt, sin, cos, max, min = math.abs, math.sqrt, math.sin, math.cos, math.max, math.min
    local BODY_W, BODY_H, GAP, ORBIT, RADIUS = 4.6, 6, 0.4, 10, 5
    local OFF_PRIM, OFF_CF = 0x178, 0xB0
    local hasMem = type(memory_read) == "function" and type(memory_write) == "function"
    local WS = game:GetService("Workspace")

    local function try(f, ...) local ok, a = pcall(f, ...) if ok then return a end return nil end
    local function clamp(v, a, b) if v < a then return a end if v > b then return b end return v end

    -- 1 = InstakillOOB (preferred), 2 = plain OOB style kill part (used only when no InstakillOOB exists)
    local function killTier(name)
        local n = string.lower(tostring(name))
        if n:find("instakill", 1, true) then return 1 end
        if n:find("oob", 1, true) or n:find("killbrick", 1, true) or n:find("killpart", 1, true) then return 2 end
        return nil
    end

    -- part CFrame from the Primitive (rotation matters for tilted kill boxes); falls back to Position only
    local function partCF(part)
        local pos = try(function() return part.Position end)
        if hasMem then
            local a = try(function() return part.Address end)
            if a and a ~= 0 then
                local p = memory_read("uintptr_t", a + OFF_PRIM)
                if p and p > 0x10000 then
                    local c, good = {}, true
                    for i = 0, 11 do
                        local v = memory_read("float", p + OFF_CF + i * 4)
                        if type(v) ~= "number" or v ~= v or v > 1e12 or v < -1e12 then good = false break end
                        c[i + 1] = v
                    end
                    if good and abs(c[1] * c[1] + c[2] * c[2] + c[3] * c[3] - 1) < 0.1 then
                        local dx, dy, dz = 0, 0, 0
                        if pos then dx, dy, dz = c[10] - pos.X, c[11] - pos.Y, c[12] - pos.Z end
                        if sqrt(dx * dx + dy * dy + dz * dz) < 3 then
                            return CFrame.new(c[10], c[11], c[12], c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8], c[9])
                        end
                    end
                end
            end
        end
        if pos then return CFrame.new(pos.X, pos.Y, pos.Z) end
        return nil
    end

    local function addrOf(i) return tostring(try(function() return i.Address end)) end

    -- (re)scan when the map changes or nothing has been found yet
    function M.scan(force)
        if M.scanning then return end
        local now = tick()
        local arena = WS:FindFirstChild("Arena")
        local bars = arena and arena:FindFirstChild("Barriers")
        local kids = 0
        if bars then kids = #bars:GetChildren() end
        local sig = (arena and addrOf(arena) or "-") .. ":" .. (bars and addrOf(bars) or "-") .. ":" .. kids
        if not force and sig == M.sig and (#M.list > 0 or now - M.scanT < 4) then return end
        M.sig, M.scanT, M.scanning = sig, now, true
        M.status = "scanning"
        task.spawn(function()
            local t1, t2 = {}, {}
            pcall(function()
                local function walk(rootInst)
                    local d = rootInst:GetDescendants()
                    for i = 1, #d do
                        local inst = d[i]
                        if inst:IsA("BasePart") then
                            local tier = killTier(inst.Name)
                            if tier then
                                local cf = partCF(inst)
                                local size = try(function() return inst.Size end)
                                if cf and size then
                                    local dst = t1
                                    if tier == 2 then dst = t2 end
                                    if #dst < 300 then dst[#dst + 1] = { cf = cf, size = size } end
                                end
                            end
                        end
                        if i % 250 == 0 then task.wait() end
                    end
                end
                if bars then walk(bars) end
                if #t1 == 0 and #t2 == 0 and arena then walk(arena) end
                if #t1 == 0 and #t2 == 0 then walk(WS) end
            end)
            local out, label = t1, "InstakillOOB"
            if #t1 == 0 then out, label = t2, "OOB (no InstakillOOB on this map)" end
            M.list, M.sel, M.key, M.pickT = out, nil, nil, 99
            M.scanning = false
            M.status = #out > 0 and ("ready: " .. #out .. " x " .. label) or "no InstakillOOB / OOB found"
        end)
    end

    function M.reset()
        M.sel, M.key, M.ang, M.pickT = nil, nil, 0, 99
    end

    local function clips(pos, hb)
        for i = 1, #M.list do
            local e = M.list[i]
            local cf = e.cf
            local lp = cf:PointToObjectSpace(pos)
            local ax, ay, az = cf.RightVector, cf.UpVector, cf.LookVector
            local ex = abs(ax.X) * hb.X + abs(ax.Y) * hb.Y + abs(ax.Z) * hb.Z
            local ey = abs(ay.X) * hb.X + abs(ay.Y) * hb.Y + abs(ay.Z) * hb.Z
            local ez = abs(az.X) * hb.X + abs(az.Y) * hb.Y + abs(az.Z) * hb.Z
            if abs(lp.X) <= e.size.X / 2 + ex and abs(lp.Y) <= e.size.Y / 2 + ey and abs(lp.Z) <= e.size.Z / 2 + ez then
                return true
            end
        end
        return false
    end

    -- pos: where you are (or your anchor).  Returns the Vector3 to stand at this frame, or nil.
    function M.park(pos, dt)
        M.scan(false)
        local list = M.list
        if #list == 0 then
            if not M.scanning then M.status = "no InstakillOOB / OOB found" end
            return nil
        end
        M.pickT = M.pickT + dt
        if not M.sel or M.pickT >= 1.5 then
            M.pickT = 0
            local best, bestD, bestLp
            for i = 1, #list do
                local e = list[i]
                local lp = e.cf:PointToObjectSpace(pos)
                local ox = max(abs(lp.X) - e.size.X / 2, 0)
                local oy = max(abs(lp.Y) - e.size.Y / 2, 0)
                local oz = max(abs(lp.Z) - e.size.Z / 2, 0)
                local d = ox * ox + oy * oy + oz * oz
                if not bestD or d < bestD then best, bestD, bestLp = e, d, lp end
            end
            local half = { best.size.X / 2, best.size.Y / 2, best.size.Z / 2 }
            local l = { bestLp.X, bestLp.Y, bestLp.Z }
            local axis, worst = 1, -1e18
            for a = 1, 3 do
                local ex = abs(l[a]) - half[a]
                if ex > worst then worst, axis = ex, a end
            end
            local sign = 1
            if l[axis] < 0 then sign = -1 end
            local key = tostring(best) .. ":" .. axis .. ":" .. sign
            local u, v = 1, 2
            if axis == 1 then u, v = 2, 3 elseif axis == 2 then u, v = 1, 3 else u, v = 1, 2 end
            if key ~= M.key then
                M.key = key
                local lu, lv = max(0, half[u] - 1), max(0, half[v] - 1)
                M.cu, M.cv = clamp(l[u], -lu, lu), clamp(l[v], -lv, lv)
            end
            M.sel = { e = best, axis = axis, sign = sign, u = u, v = v, half = half }
        end
        local s = M.sel
        M.ang = M.ang + ORBIT * dt
        local half, u, v = s.half, s.u, s.v
        local r = max(1, min(RADIUS, half[u] - 2, half[v] - 2))
        local pt = { 0, 0, 0 }
        pt[s.axis] = s.sign * half[s.axis]
        pt[u] = clamp(M.cu + cos(M.ang) * r, -half[u], half[u])
        pt[v] = clamp(M.cv + sin(M.ang) * r, -half[v], half[v])
        local cf = s.e.cf
        local surface = cf:PointToWorldSpace(Vector3.new(pt[1], pt[2], pt[3]))
        local unit = { 0, 0, 0 }
        unit[s.axis] = s.sign
        local N = cf:PointToWorldSpace(Vector3.new(unit[1], unit[2], unit[3])) - cf.Position
        local hb = Vector3.new(BODY_W / 2, BODY_H / 2, BODY_W / 2)
        local ext = abs(N.X) * hb.X + abs(N.Y) * hb.Y + abs(N.Z) * hb.Z
        local out = surface + N * (ext + GAP)
        for _ = 1, 4 do
            if not clips(out, hb) then break end
            out = out + N * 1
        end
        M.status = "orbiting"
        return out
    end

    return M
end)
if not Translocate_ok then
    K.errors.translocate_load = tostring(Translocate)
    Translocate = { list = {}, status = "module failed to load", scan = function() end, reset = function() end, park = function() return nil end }
end

--------------------------------------------------------------------------
-- RAGEBOT
--   Silent aim   : the cursor/camera is never touched.  On a strike frame your
--                  HumanoidRootPart is moved ALONG YOUR OWN VIEW RAY so the target's
--                  head sits exactly under the crosshair, then mouse1click fires.
--   Off          : strike every frame, never evade
--   Random       : strike frame -> silent aim + fire ; other frames -> hop to a
--                  random point on a ring around the anchor
--   Translocate  : strike frame -> silent aim + fire ; other frames -> the shared
--                  Translocate module (snap beside the nearest InstakillOOB and orbit)
--   No desync, no remotes.
--------------------------------------------------------------------------
local Rage = { engaged = false, frame = 0, anchor = nil, status = "Idle", tp = "untested", target = nil, away = false, camOff = nil, lastT = 0, dt = 1 / 60 }

local function setPos(root, v3)
    local ok = pcall(function() root.Position = v3 end)
    return ok
end
local function zeroVel(root)
    pcall(function() root.AssemblyLinearVelocity = Vector3.new(0, 0, 0) end)
end
local function pressKey(vk)
    task.spawn(function() keypress(vk) wait(0.03) keyrelease(vk) end)
end

function Rage.pick(c, myPos, ox, oy)
    local best, bestScore
    for _, e in ipairs(Targets.list) do
        if e.alive and (not c.teamCheck or e.enemy) then
            local ok, p = pcall(Targets.pos, e, "Head")
            if ok then
                local d = (p - myPos).Magnitude
                if d <= c.maxDist then
                    local score
                    if c.priority == "Closest" then
                        score = d
                    elseif c.priority == "Lowest Health" then
                        score = e.hp
                    else
                        local sx, sy = w2s(p)
                        if sx then score = (sx - ox) ^ 2 + (sy - oy) ^ 2 else score = 1e12 + d end
                    end
                    if not bestScore or score < bestScore then best, bestScore = e, score end
                end
            end
        end
    end
    return best
end

-- Silent aim: put the camera on the line (head - look * dist). The camera never turns,
-- the crosshair already points at the head from there.
function Rage.silentPos(c, headPos)
    local look = Cam.look()
    local off = Rage.camOff or Vector3.new(0, 1.5, 0)
    if look and string.sub(Cam.mode, 1, 6) == "memory" then
        Rage.silentNote = nil
        return headPos - look * c.glue.dist - off
    end
    -- no camera memory: stand c.glue.dist from the head on the side we are already on
    local mine = Rage.anchor or headPos
    local d = mine - headPos
    if d.Magnitude < 0.5 then d = Vector3.new(0, 0, 1) end
    Rage.silentNote = "no camera memory: positioned beside target"
    return headPos + d.Unit * c.glue.dist - off + Vector3.new(0, 1.5, 0)
end
function Rage.evadePos(c, headPos)
    local ev = c.evasion
    if ev.mode == "Translocate" then
        return Translocate.park(Rage.anchor, Rage.dt)
    end
    local a
    if ev.anchor == "Character" then a = Rage.anchor
    elseif ev.anchor == "Origin" then a = Vector3.new(0, Rage.anchor.Y, 0)
    else a = headPos end
    local ang = random() * pi * 2
    local r = ev.radius + ev.radius * ev.factor * random()
    return a + Vector3.new(cos(ang) * r, (random() * 2 - 1) * ev.yRange, sin(ang) * r)
end

function Rage.disengage(root)
    if Rage.anchor and root and Rage.away then
        setPos(root, Rage.anchor)
        zeroVel(root)
    end
    Translocate.reset()
    Rage.engaged, Rage.away, Rage.anchor, Rage.target = false, false, nil, nil
    Rage.status = "Idle"
end

function Rage.tick()
    local c = Cfg.Ragebot
    local root = myParts()
    if not featureOn(c) then
        if Rage.engaged then Rage.disengage(root) end
        return
    end
    if not root then Rage.status = "No character" return end
    if not Rage.engaged then
        Rage.engaged = true
        Rage.anchor = root.Position
        Rage.frame = 0
        Translocate.reset()
        Translocate.scan(true)
        local cam0 = camera()
        local cp0 = cam0 and try(function() return cam0.Position end)
        Rage.camOff = nil
        if cp0 then
            local d0 = cp0 - root.Position
            if d0.Magnitude < 25 then Rage.camOff = d0 end
        end
        if c.equip ~= "Off" then
            local vk = 0x31
            if c.equip == "Secondary" then vk = 0x32 elseif c.equip == "Melee" then vk = 0x33 end
            pressKey(vk)
        end
    end
    local nowT = tick()
    Rage.dt = clamp(nowT - Rage.lastT, 0.001, 0.1)
    Rage.lastT = nowT
    Rage.frame = Rage.frame + 1

    local ox, oy = aimOrigin({ origin = "Center" })
    local tgt = Rage.pick(c, Rage.anchor or root.Position, ox, oy)
    Rage.target = tgt
    if not tgt then
        if Rage.away then setPos(root, Rage.anchor); zeroVel(root); Rage.away = false end
        Rage.status = "No target"
        return
    end

    local ok, headPos = pcall(Targets.pos, tgt, "Head")
    if not ok then return end
    local sf = max(1, floor(c.shootFrames))
    local ef = 0
    if c.evasion.mode ~= "Off" then ef = max(1, floor(c.evasion.evadeFrames)) end
    local phase = Rage.frame % (sf + ef)
    local strike = phase < sf
    local fireFrame = strike and phase == sf - 1

    if strike then
        local glue = Rage.silentPos(c, headPos)
        if not glue then
            Rage.status = "No position for silent aim"
            return
        end
        local wrote = setPos(root, glue)
        zeroVel(root)
        Rage.away = true
        if Rage.tp == "untested" and wrote then
            local back = try(function() return root.Position end)
            if back then
                if (back - glue).Magnitude < 15 then Rage.tp = "OK" else Rage.tp = "FAIL (position write ignored)" end
            end
        elseif not wrote then
            Rage.tp = "FAIL (write error)"
        end
        Rage.status = "Silent aim " .. tgt.name .. (Rage.silentNote and (" (" .. Rage.silentNote .. ")") or "")

        if K.ui.open or not isrbxactive() then return end
        if c.autoFire and fireFrame then mouse1click() end
    else
        local ep = Rage.evadePos(c, headPos)
        if ep then
            setPos(root, ep)
            zeroVel(root)
            Rage.away = true
            Rage.status = "Evading (" .. c.evasion.mode .. ")"
        else
            Rage.status = c.evasion.mode .. ": " .. Translocate.status
        end
    end
end
--------------------------------------------------------------------------
-- movement: fly / speed / noclip / infinite jump  (documented APIs only)
--------------------------------------------------------------------------
local Move = { flying = false, noclipT = 0, jumpPrev = false }
local function moveDir(look, includeVertical)
    local f = Vector3.new(look.X, 0, look.Z)
    if includeVertical then f = look end
    if f.Magnitude < 0.01 then f = Vector3.new(0, 0, -1) end
    f = f.Unit
    local rgt = Vector3.new(-f.Z, 0, f.X)
    if includeVertical then rgt = Vector3.new(-look.Z, 0, look.X) if rgt.Magnitude < 0.01 then rgt = Vector3.new(1, 0, 0) end rgt = rgt.Unit end
    local d = Vector3.new(0, 0, 0)
    if keyDown(0x57) then d = d + f end
    if keyDown(0x53) then d = d - f end
    if keyDown(0x44) then d = d + rgt end
    if keyDown(0x41) then d = d - rgt end
    return d
end

function Move.tick(dt)
    local root = myParts()
    local fly, spd, nc, jmp = Cfg.Movement.fly, Cfg.Movement.speed, Cfg.Movement.noclip, Cfg.Movement.jump
    local active = isrbxactive() and not K.ui.open

    -- fly
    if featureOn(fly) and root then
        if not Move.flying then
            Move.flying = true
            if World.ptr ~= 0 then
                K.flyGravity = true
                World.grav0 = World.grav0 or World.get(OFF.WorldGravity) or 196.2
                World.set(OFF.WorldGravity, 0)
            end
        end
        local look = Cam.look()
        local dir = Vector3.new(0, 0, 0)
        if active and look then
            dir = moveDir(look, true)
            if keyDown(0x20) then dir = dir + Vector3.new(0, 1, 0) end
            if keyDown(0x10) or keyDown(0xA0) then dir = dir - Vector3.new(0, 1, 0) end
        end
        if fly.mode == "Position" then
            pcall(function() root.AssemblyLinearVelocity = Vector3.new(0, 0, 0) end)
            if dir.Magnitude > 0.01 then setPos(root, root.Position + dir.Unit * fly.speed * dt) end
        else
            local v = Vector3.new(0, 0, 0)
            if dir.Magnitude > 0.01 then v = dir.Unit * fly.speed end
            pcall(function() root.AssemblyLinearVelocity = v end)
        end
    elseif Move.flying then
        Move.flying = false
        if K.flyGravity then
            K.flyGravity = false
            if World.ptr ~= 0 then
                World.set(OFF.WorldGravity, World.grav0 or 196.2)
                World.grav0 = nil
            end
        end
        if root then pcall(function() root.AssemblyLinearVelocity = Vector3.new(0, 0, 0) end) end
    end

    -- speed (horizontal velocity override while a movement key is held)
    if featureOn(spd) and root and active and not Move.flying then
        local look = Cam.look()
        if look then
            local d = moveDir(look, false)
            if d.Magnitude > 0.01 then
                local cur = try(function() return root.AssemblyLinearVelocity end)
                local y = cur and cur.Y or 0
                local h = d.Unit * spd.value
                pcall(function() root.AssemblyLinearVelocity = Vector3.new(h.X, y, h.Z) end)
            end
        end
    end

    -- noclip
    if featureOn(nc) and root then
        local now = tick()
        if now - Move.noclipT > 0.2 then
            Move.noclipT = now
            local ch = LocalPlayer.Character
            if ch then
                for _, part in ipairs(ch:GetDescendants()) do
                    if part:IsA("BasePart") then pcall(function() part.CanCollide = false end) end
                end
            end
        end
    end

    -- infinite jump
    local down = keyDown(0x20)
    if featureOn(jmp) and root and active and down and not Move.jumpPrev then
        local cur = try(function() return root.AssemblyLinearVelocity end)
        if cur then pcall(function() root.AssemblyLinearVelocity = Vector3.new(cur.X, jmp.power, cur.Z) end) end
    end
    Move.jumpPrev = down
end

--------------------------------------------------------------------------
-- ESP
--------------------------------------------------------------------------
local R15 = {
    { "Head", "UpperTorso" }, { "UpperTorso", "LowerTorso" }, { "UpperTorso", "LeftUpperArm" },
    { "LeftUpperArm", "LeftLowerArm" }, { "LeftLowerArm", "LeftHand" }, { "UpperTorso", "RightUpperArm" },
    { "RightUpperArm", "RightLowerArm" }, { "RightLowerArm", "RightHand" }, { "LowerTorso", "LeftUpperLeg" },
    { "LeftUpperLeg", "LeftLowerLeg" }, { "LeftLowerLeg", "LeftFoot" }, { "LowerTorso", "RightUpperLeg" },
    { "RightUpperLeg", "RightLowerLeg" }, { "RightLowerLeg", "RightFoot" },
}
local R6 = {
    { "Head", "Torso" }, { "Torso", "Left Arm" }, { "Torso", "Right Arm" }, { "Torso", "Left Leg" }, { "Torso", "Right Leg" },
}

local Esp = {}
local function drawBoxFull(x, y, w, h, color)
    R.border(x - 1, y - 1, w + 2, h + 2, 0, 1)
    R.border(x + 1, y + 1, w - 2, h - 2, 0, 1)
    R.border(x, y, w, h, color, 1)
end
local function drawBoxCorner(x, y, w, h, color)
    local l = max(4, min(w, h) * 0.28)
    local function seg(x1, y1, x2, y2)
        R.line(x1, y1, x2, y2, 0, 3)
        R.line(x1, y1, x2, y2, color, 1)
    end
    seg(x, y, x + l, y) seg(x, y, x, y + l)
    seg(x + w, y, x + w - l, y) seg(x + w, y, x + w, y + l)
    seg(x, y + h, x + l, y + h) seg(x, y + h, x, y + h - l)
    seg(x + w, y + h, x + w - l, y + h) seg(x + w, y + h, x + w, y + h - l)
end

local function espEntry(e, sc, myPos, vw, vh)
    local rootPos = e.root.Position
    local dist = (rootPos - myPos).Magnitude
    if dist > Cfg.Esp.maxDist then return end
    local headPos = e.head and e.head.Position or (rootPos + Vector3.new(0, 1.5, 0))
    local tx, ty = w2s(headPos + Vector3.new(0, 0.65, 0))
    local bx, by = w2s(rootPos - Vector3.new(0, 3, 0))
    if not tx or not bx then return end
    local h = by - ty
    if h < 4 then return end
    local w = h * 0.55
    local left = tx - w / 2
    local ts = Cfg.Esp.textSize

    if sc.box.on then
        if sc.box.style == "Corner" then drawBoxCorner(left, ty, w, h, sc.box.color) else drawBoxFull(left, ty, w, h, sc.box.color) end
    end
    if sc.health.on then
        local p = clamp(e.hp / e.maxhp, 0, 1)
        R.rect(left - 6, ty - 1, 4, h + 2, 0)
        R.rect(left - 5, ty + h * (1 - p), 2, h * p, pack(255 * (1 - p), 255 * p, 40))
    end
    if sc.name.on then
        local tw = R.tw(e.name, ts)
        R.text(tx - tw / 2, ty - ts - 4, e.name, ts, sc.name.color, false, true)
    end
    local ly = by + 2
    if sc.healthNum.on then
        local s = tostring(floor(e.hp))
        R.text(tx - R.tw(s, ts) / 2, ly, s, ts, sc.healthNum.color, false, true)
        ly = ly + ts + 1
    end
    if sc.distance.on then
        local s = fmt("[%dm]", floor(dist))
        R.text(tx - R.tw(s, ts) / 2, ly, s, ts, sc.distance.color, false, true)
    end
    if sc.tracer.on then
        local fx, fy = vw / 2, vh
        local o = sc.tracer.origin
        if o == "Center" then fy = vh / 2 elseif o == "Top" then fy = 0 elseif o == "Mouse" then fx, fy = I.mx, I.my end
        R.line(fx, fy, bx, by, 0, 3)
        R.line(fx, fy, bx, by, sc.tracer.color, 1)
    end
    if sc.head.on then
        local hx, hy = w2s(headPos)
        if hx then
            local r = max(2, h * 0.07)
            R.circle(hx, hy, r + 1, 0, false, 3, 20)
            R.circle(hx, hy, r, sc.head.color, false, 1, 20)
        end
    end
    if sc.skeleton.on and dist < 400 then
        local pairsList = R6
        if e.char:FindFirstChild("UpperTorso") then pairsList = R15 end
        for _, pr in ipairs(pairsList) do
            local a, b = e.char:FindFirstChild(pr[1]), e.char:FindFirstChild(pr[2])
            if a and b then
                local ax, ay = w2s(a.Position)
                local bx2, by2 = w2s(b.Position)
                if ax and bx2 then R.line(ax, ay, bx2, by2, sc.skeleton.color, 1) end
            end
        end
    end
end

function Esp.draw()
    local c = Cfg.Esp
    if not featureOn(c) then return end
    local vw, vh = viewport()
    local root = myParts()
    local myPos = root and root.Position or (camera() and camera().Position) or Vector3.new(0, 0, 0)
    for _, e in ipairs(Targets.list) do
        if e.alive then
            local sc = e.enemy and c.Enemy or c.Team
            if sc.enabled then pcall(espEntry, e, sc, myPos, vw, vh) end
        end
    end
end

local function drawCrosshair()
    local c = Cfg.Crosshair
    if not c.enabled then return end
    local vw, vh = viewport()
    local cx, cy = vw / 2, vh / 2
    local s, g, t = c.size, c.gap, c.thick
    local function bar(x, y, w, h)
        R.rect(x - 1, y - 1, w + 2, h + 2, 0)
        R.rect(x, y, w, h, c.color)
    end
    bar(cx - g - s, cy - t / 2, s, t)
    bar(cx + g, cy - t / 2, s, t)
    bar(cx - t / 2, cy - g - s, t, s)
    bar(cx - t / 2, cy + g, t, s)
    if c.dot then bar(cx - t / 2, cy - t / 2, t, t) end
end

local function drawFov()
    local c = Cfg.Aimbot
    if not (c.enabled and c.showFov) then return end
    local ox, oy = aimOrigin(c)
    R.circle(ox, oy, c.fov, c.fovColor, false, 1, 64)
end

--------------------------------------------------------------------------
-- UI : lolcat layout (919x643 window, 100px rail, 17px grid gap, 12px padding)
--------------------------------------------------------------------------
local UI = {
    open = true, x = nil, y = nil, tab = 1, sub = {}, scroll = {}, popup = nil, active = nil,
    drag = nil, capture = nil,
}
K.ui = UI
local WIN_W, WIN_H, RAIL_W, OUTER, GAPX = 919, 643, 100, 18, 17
local HEAD_H, STRIP_H = 85, 84

-- tiny vector glyphs for the rail icons
local Glyph = {}
function Glyph.crosshair(cx, cy, c)
    R.circle(cx, cy, 8, c, false, 1.5, 24)
    R.line(cx - 12, cy, cx - 4, cy, c, 1.5) R.line(cx + 4, cy, cx + 12, cy, c, 1.5)
    R.line(cx, cy - 12, cx, cy - 4, c, 1.5) R.line(cx, cy + 4, cx, cy + 12, c, 1.5)
end
function Glyph.player(cx, cy, c)
    R.circle(cx, cy - 6, 5, c, false, 1.5, 20)
    R.rect(cx - 9, cy + 2, 18, 9, c, 4)
    R.rect(cx - 7, cy + 4, 14, 6, T.GradientMid, 3)
end
function Glyph.eye(cx, cy, c)
    R.circle(cx, cy, 10, c, false, 1.5, 24)
    R.circle(cx, cy, 4, c, true, 1, 16)
end
function Glyph.globe(cx, cy, c)
    R.circle(cx, cy, 10, c, false, 1.5, 28)
    R.line(cx - 10, cy, cx + 10, cy, c, 1) R.line(cx, cy - 10, cx, cy + 10, c, 1)
    R.circle(cx, cy, 5, c, false, 1, 20)
end
function Glyph.skin(cx, cy, c)
    R.rect(cx - 11, cy - 9, 22, 15, c, 3)
    R.rect(cx - 9, cy - 7, 18, 11, T.GradientMid, 2)
    R.circle(cx - 4, cy - 2, 2, c, true, 1, 10)
    R.circle(cx + 2, cy - 4, 2, c, true, 1, 10)
    R.circle(cx + 5, cy + 1, 2, c, true, 1, 10)
    R.rect(cx - 4, cy + 8, 8, 3, c, 1)
end
function Glyph.gun(cx, cy, c)
    R.rect(cx - 12, cy - 8, 24, 7, c, 2)
    R.rect(cx - 12, cy - 8, 4, 10, c, 1)
    R.rect(cx - 5, cy - 1, 7, 11, c, 2)
    R.rect(cx + 2, cy - 1, 6, 2, c, 1)
    R.rect(cx - 2, cy - 6, 12, 3, T.GradientMid, 1)
end
function Glyph.gear(cx, cy, c)
    R.circle(cx, cy, 8, c, false, 2, 20)
    R.circle(cx, cy, 3, c, true, 1, 12)
    R.rect(cx - 2, cy - 12, 4, 5, c) R.rect(cx - 2, cy + 7, 4, 5, c)
    R.rect(cx - 12, cy - 2, 5, 4, c) R.rect(cx + 7, cy - 2, 5, 4, c)
end

-- descriptor constructors -------------------------------------------------
local function Toggle(label, tbl, key, o)
    o = o or {}
    return { t = "toggle", label = label, tbl = tbl, key = key, bind = o.bind, color = o.color, show = o.show, a = tbl[key] and 1 or 0 }
end
local function Slider(label, tbl, key, mn, mx, step, suffix, show)
    return { t = "slider", label = label, tbl = tbl, key = key, min = mn, max = mx, step = step or 1, suffix = suffix or "", show = show }
end
local function Drop(label, tbl, key, opts, show)
    return { t = "drop", label = label, tbl = tbl, key = key, opts = opts, show = show }
end
local function Button(label, fn, show) return { t = "button", label = label, fn = fn, show = show } end
local function Stat(label, getter, show) return { t = "stat", label = label, get = getter, show = show } end
local function KeyRow(label, tbl, key, show) return { t = "keyrow", label = label, tbl = tbl, key = key, show = show } end
local function Divider(label, show) return { t = "divider", label = label, show = show } end

-- diagnostics ---------------------------------------------------------------
local fpsAvg = 60
function K.diag()
    local root, ch = myParts()
    local cam = camera()
    local vw, vh = viewport()
    local lines = {}
    local function add(s) lines[#lines + 1] = s end
    local ex, ver = "?", "?"
    pcall(function() ex, ver = identifyexecutor() end)
    add(fmt("Executor: %s %s | Game: %s | Place: %s", tostring(ex), tostring(ver), tostring(try(getgamename)), tostring(try(function() return game.PlaceId end))))
    add(fmt("Players: %d | tracked targets: %d", #Players:GetPlayers(), #Targets.list))
    add(fmt("LocalPlayer char: %s | HRP: %s", tostring(ch ~= nil), tostring(root ~= nil)))
    add(fmt("Viewport: %dx%d | Mouse: %d,%d | FPS: %d | Ping: %s", vw, vh, I.mx, I.my, floor(fpsAvg), tostring(try(GetPingValue))))
    add(fmt("Memory API: %s | World ptr: %s", tostring(hasMem), World.ptr ~= 0 and fmt("0x%X", World.ptr) or "none"))
    add(fmt("Translocate: %s (%d kill parts) | Cam look: %s", Translocate.status, #Translocate.list, Cam.mode))
    add(fmt("Camera look: %s | camera ptr: %s", Cam.mode, tostring(cam and try(function() return cam.Address end))))
    add(fmt("Teleport write: %s | Ragebot: %s", Rage.tp, Rage.status))
    add(fmt("Silent aim: %s | shots %d | cam choice %s", K.ext.SA.status, K.ext.SA.shots, tostring(Cam.choice)))
    add(fmt("Gun mods: %s | getgc available: %s", K.ext.Gun.status, tostring(type(getgc) == "function")))
    local le = {}
    for k, v in pairs(K.ext.Lit.errors) do le[#le + 1] = k .. "=" .. tostring(v) end
    add(fmt("Lighting: %s | sky: %s | rejected: %s", K.ext.Lit.status, tostring(K.ext.Lit.skyStatus), #le > 0 and table.concat(le, "; ") or "none"))
    add(fmt("Skin changer: %s | %s", K.ext.SC.S.status, K.ext.SC.invStatus()))
    local bp = {}
    for k, v in pairs(K.badProps) do bp[#bp + 1] = k .. " (" .. tostring(v) .. ")" end
    add(fmt("Draw: text size prop = %s | rejected props: %s", tostring(K.textSizeProp), #bp > 0 and table.concat(bp, "; ") or "none"))
    local n = 0
    for k, v in pairs(K.errors) do n = n + 1 add(fmt("ERR[%s]: %s", k, tostring(v))) end
    if n == 0 then add("Errors: none") end
    return table.concat(lines, "\n")
end

--------------------------------------------------------------------------
-- EXTRAS: widgets for custom pages, Skin Changer, Gun / Melee mods, Silent Aim, World FX
-- (all in one function so the main chunk keeps its local count low)
--------------------------------------------------------------------------
local Ext = (function()
    local X = { links = {} }
    local SC, Gun, SA, FX, Lit = {}, {}, {}, {}, {}
    X.SC, X.Gun, X.SA, X.FX, X.Lit = SC, Gun, SA, FX, Lit

    local function numbered(prefix, from, to)
        local out = {}
        for n = from, to do out[#out + 1] = fmt("%s %02d", prefix, n) end
        return out
    end
    X.SKY_GROUPS = {
        { name = "Game skies", skies = { "blue", "space", "graveyard", "sudden death", "station", "westown", "black", "gray", "classic" } },
        { name = "Cloudy", skies = numbered("cloudy", 1, 25) },
        { name = "Space", skies = { "galaxy", "blue nebula", "gold nebula" } },
        { name = "More A-D", skies = { "aurora", "beautiful", "black hole", "blue sky", "broken sky", "castle grounds", "chill gray", "chill pink", "chroma key", "clear skies", "cyan", "dead star forest", "disaster" } },
        { name = "More E-M", skies = { "elegant morning", "emo", "fade blue", "forest", "goodnight", "grimnight", "hades", "hazy", "jungle", "light blue", "light pink", "minecraft", "minecraft end" } },
        { name = "More M-P", skies = { "moonlight", "neon sky", "neon sky 2", "nibiru", "night", "night sky moon", "northern lights", "oblivion", "orange", "overcast", "pandora", "peaceful morning", "pink sunrise" } },
        { name = "More P-S", skies = { "pumpkin hill", "purple nebula", "red", "setting sun", "sfoth", "shiverfrost", "sky 05", "sky 13", "sky 2006", "sky 22", "sky 31", "sky 38", "sky 47" } },
        { name = "More S-Z", skies = { "sky purple", "sky sunset", "space blue", "spooky", "sunny sky", "universe", "utter east", "whomp fortress", "winterness", "xen", "zen end" } },
    }
    X.SOUNDS = {
        { name = "Rivals", sounds = {
            { "Hitmarker tick", "13110130082" }, { "Headshot crack", "16537449730" }, { "Elimination 1", "16530229616" },
            { "Elimination 2", "16530229541" }, { "Elimination 3", "16530229695" }, { "Target shatter", "14441658101" },
            { "RPG explosion", "13455969017" }, { "Equip click", "13158735106" }, { "Click", "177266782" } } },
        { name = "Roblox", sounds = {
            { "Classic hit", "12222046" }, { "Button", "12221967" }, { "Electronic ping", "12221990" }, { "Glass break", "12222005" },
            { "Kerplunk", "12222054" }, { "Bright click", "15675059323" }, { "Cute pop", "15675055424" }, { "Coin", "127645268874265" },
            { "Pinball bell", "16480570986" }, { "8-bit blip", "16480580213" }, { "Sparkle ding", "9126073001" }, { "Cannon blast", "3149249837" } } },
        { name = "Hit sounds", sounds = {
            { "Undertale critical hit", "140181868959125" }, { "Hit sound", "139520673393967" }, { "Fist hit", "140604838213617" },
            { "TF2 critical hit", "137392628136734" }, { "Rock hit", "82708037443413" }, { "Persona 5 hit", "140706017778464" },
            { "Energy sword hit", "139503070303020" }, { "Stone hit", "3581383408" }, { "8-bit impact", "109598434966968" },
            { "Minecraft hit", "73369656122118" }, { "Beam hit", "103134129110384" } } },
        { name = "Community", sounds = {
            { "CoD hitmarker", "138832207290954" }, { "Quake hitmarker", "1455817260" }, { "GameSense hitmarker", "4817809188" },
            { "Minecraft hitmarker", "127091812835195" }, { "MLG hitmarker", "121351852050830" }, { "TF2 hitsound", "138901307926331" },
            { "osu! hitsound", "123941247147792" }, { "CS:GO headshot", "133002449941130" }, { "Arsenal headshot", "18513634637" },
            { "Fortnite headshot", "2513174484" }, { "Rust headshot", "128633263668964" }, { "Battlefield headshot", "70528023820006" },
            { "TF2 kill", "124543461907751" }, { "Among Us kill", "130456049552264" }, { "Double kill", "116907610084760" },
            { "skeet (louder)", "140247876667835" }, { "neverlose.cc", "139452805868562" }, { "Fatality", "97439296876895" } } },
    }

    ----------------------------------------------------------------------
    -- widgets (press-edge clicks like the rest of the menu)
    ----------------------------------------------------------------------
    local function live(x, y, w, h)
        if UI.popup or not I.inside(x, y, w, h) then return false end
        local cl = R.clip
        if cl and not I.inside(cl[1], cl[2], cl[3] - cl[1], cl[4] - cl[2]) then return false end
        return true
    end
    local function click(x, y, w, h)
        if I.pressed and live(x, y, w, h) then I.pressed = false return true end
        return false
    end
    local function fit(s, w, size)
        s = tostring(s)
        if R.tw(s, size) <= w then return s end
        local n = floor(w / (size * 0.52)) - 2
        if n < 1 then return "" end
        return s:sub(1, n) .. ".."
    end
    local function box(x, y, w, h, hot)
        R.rect(x - 1, y - 1, w + 2, h + 2, T.Outline, 6)
        R.rect(x, y, w, h, hot and T.GradientTop or T.GradientMid, 5)
    end
    local function btn(x, y, w, h, label, primary, disabled)
        local hot = (not disabled) and live(x, y, w, h)
        R.rect(x - 1, y - 1, w + 2, h + 2, T.Outline, 6)
        local bg = T.GradientMid
        if primary then bg = hot and mix(T.Accent, T.White, 0.18) or T.Accent
        elseif hot then bg = T.GradientTop end
        R.rect(x, y, w, h, bg, 5)
        local col = T.TextColor
        if disabled then col = T.Unselected elseif primary then col = pack(8, 10, 10) elseif hot then col = T.Accent end
        R.text(x + (w - R.tw(label, 14)) / 2, y + (h - 14) / 2 - 1, label, 14, col, primary == true)
        return (not disabled) and click(x, y, w, h)
    end
    local function seg(x, y, w, h, labels, sel)
        box(x, y, w, h, false)
        local each, picked = w / #labels, nil
        for i, l in ipairs(labels) do
            local bx = x + (i - 1) * each
            if i == sel then
                R.rect(bx + 2, y + 2, each - 4, h - 4, T.TabButtonSelected, 4)
                R.rect(bx + each * 0.25, y + h - 4, each * 0.5, 2, T.Accent, 1)
            end
            R.text(bx + (each - R.tw(l, 13)) / 2, y + (h - 13) / 2 - 1, l, 13, i == sel and T.Accent or T.Unselected, i == sel)
            if click(bx, y, each, h) then picked = i end
        end
        return picked
    end

    -- text boxes ----------------------------------------------------------
    local TI = { focus = nil, text = {}, bsAt = 0 }
    X.TI = TI
    local keyPrev = {}
    local function keyHit(vk)
        local d = keyDown(vk)
        local was = keyPrev[vk]
        keyPrev[vk] = d
        return d and not was, d
    end
    local TYPED = {}
    for i = 0, 25 do TYPED[0x41 + i] = { string.char(97 + i), string.char(65 + i) } end
    for i = 0, 9 do TYPED[0x30 + i] = { tostring(i), (")!@#$%^&*("):sub(i + 1, i + 1) } end
    TYPED[0x20] = { " ", " " } TYPED[0xBD] = { "-", "_" } TYPED[0xBE] = { ".", ">" } TYPED[0xDE] = { "'", '"' }
    function TI.tick()
        if not UI.open then TI.focus = nil end
        local id = TI.focus
        if not id then return end
        local v = TI.text[id] or ""
        local shift = select(2, keyHit(0x10))
        for vk, ch in pairs(TYPED) do
            if keyHit(vk) then v = v .. ch[shift and 2 or 1] end
        end
        local bh, bd = keyHit(0x08)
        if bh then v = v:sub(1, -2); TI.bsAt = tick() + 0.4
        elseif bd and tick() > TI.bsAt then v = v:sub(1, -2); TI.bsAt = tick() + 0.04 end
        TI.text[id] = v
        local e1, e2 = keyHit(0x0D), keyHit(0x1B)
        if e1 or e2 then TI.focus = nil end
    end
    local function tbox(id, x, y, w, h, placeholder)
        local v = TI.text[id] or ""
        local f = TI.focus == id
        if I.pressed and f and not I.inside(x, y, w, h) then TI.focus = nil; f = false end
        box(x, y, w, h, f)
        if f then R.rect(x, y + h - 2, w, 2, T.Accent, 1) end
        if v == "" and not f then
            R.text(x + 9, y + (h - 13) / 2 - 1, placeholder, 13, T.Unselected, false)
        else
            R.text(x + 9, y + (h - 13) / 2 - 1, fit(v, w - 18, 13) .. ((f and tick() % 1 < 0.5) and "|" or ""), 13, T.TextColor, false)
        end
        if click(x, y, w, h) then TI.focus = id end
        return v:lower()
    end
    local function matches(q, name) return q == "" or tostring(name):lower():find(q, 1, true) ~= nil end

    -- scroll area (arrow keys / PgUp / PgDn while pointing at it, or drag the bar) --------
    local scrollPos = {}
    local function cscroll(id, x, y, w, h, content, dt)
        local mx = max(0, content - h)
        local s = scrollPos[id] or 0
        if live(x, y, w, h) then
            if keyDown(0x28) then s = s + 600 * dt end
            if keyDown(0x26) then s = s - 600 * dt end
            if keyDown(0x22) then s = s + 1000 * dt end
            if keyDown(0x21) then s = s - 1000 * dt end
        end
        if mx > 0 then
            local bx = x + w + 4
            local th = max(30, h * h / content)
            local ty = y + (h - th) * s / mx
            R.rect(bx, y, 4, h, T.GradientTop, 2)
            R.rect(bx, ty, 4, th, T.Accent, 2)
            if I.pressed and I.inside(bx - 6, y, 16, h) and not UI.popup then
                UI.active = { kind = "cscroll", id = id, off = I.my - ty }
                I.pressed = false
            end
            local a = UI.active
            if a and a.kind == "cscroll" and a.id == id then
                if I.down then s = clamp((I.my - a.off - y) / max(1, h - th), 0, 1) * mx else UI.active = nil end
            end
        end
        s = clamp(s, 0, mx)
        scrollPos[id] = s
        return s
    end
    local function resetScroll(id) scrollPos[id] = 0 end

    ----------------------------------------------------------------------
    -- pictures from local cache & martinikaws CDN
    ----------------------------------------------------------------------
    local SITE = "https://martinikaws.github.io/rivals-skins/"
    local CACHE = "lolcat_imgcache"
    local images = {}
    local downloading = {}
    local function cachePath(p) return CACHE .. "/" .. p:gsub("[^%w%-_%.]", "_") .. ".dat" end
    local function fetchImage(path)
        if not path or path == "" or downloading[path] then return end
        downloading[path] = true
        task.spawn(function()
            pcall(makefolder, CACHE)
            local url = SITE .. path
            local ok, body = pcall(httpget, url)
            if (not ok or not body or #body < 10) and game and game.HttpGet then
                ok, body = pcall(function() return game:HttpGet(url) end)
            end
            if ok and type(body) == "string" and #body > 10 then
                images[path] = { data = body, state = "ok" }
                pcall(writefile, cachePath(path), body)
            else
                images[path] = { data = nil, state = "failed" }
            end
            downloading[path] = false
        end)
    end
    local function imageData(path)
        if not path or path == "" then return nil end
        local e = images[path]
        if e ~= nil then return e.data end
        local f = cachePath(path)
        local okH, has = pcall(isfile, f)
        if okH and has then
            local okR, body = pcall(readfile, f)
            if okR and type(body) == "string" and #body > 8 then
                images[path] = { data = body, state = "ok" }
                return body
            end
        end
        if not downloading[path] then
            fetchImage(path)
        end
        return nil
    end

    ----------------------------------------------------------------------
    -- Dedicated skinchanger config (Lolcatskinchanger.lua / .json) + rivals_config.lua mirror
    ----------------------------------------------------------------------
    local LOLCAT_SKIN_FILE = "Lolcatskinchanger.lua"
    local LOLCAT_SKIN_JSON = "Lolcatskinchanger.json"
    local FILE, BACKUP = "rivals_config.lua", "rivals_config.backup.lua"
    local SCRIPT_FILES = {
        "skinchanger.lua", "scripts/skinchanger.lua", "workspace/skinchanger.lua",
        "lolcat_imgcache/swapper.lua", "workspace/lolcat_imgcache/swapper.lua",
        "RivalsSkinSwapper.lua", "workspace/RivalsSkinSwapper.lua", "scripts/RivalsSkinSwapper.lua"
    }
    local RIVALS_GAME_ID = 6035872082
    local S = { lines = {}, values = {}, swaps = {}, readable = false, baseline = nil, dirty = false, cleanText = "",
        status = "Ready", busy = false, cat = { weapons = {}, wraps = {}, finishers = {}, charms = {}, skyFull = {}, skyFace = {}, loaded = true } }
    SC.S = S
    SC.autoLoad = true
    SC.autoApply = true

    local function trim(s) return s:match("^%s*(.-)%s*$") end
    local function header(line)
        local s = line:match("^%s*%[%s*(.-)%s*%]%s*$")
        return s and s:lower() or nil
    end
    local function pair(line)
        if line:match("^%s*%-%-") then return nil end
        local k, v = line:match("^%s*([^=]-)%s*=%s*(.-)%s*$")
        if k and trim(k) ~= "" then return trim(k), v end
    end
    local function swapLine(line)
        local w, owned, target = line:match("^%s*([^|]-)%s*|%s*([^>]-)%s*>%s*(.-)%s*$")
        if w and owned and target and w ~= "" and owned ~= "" and target ~= "" then return w, owned, target end
    end
    local function indexConfig()
        S.values = { skins = {}, wraps = {}, finishers = {}, charms = {}, skybox = {}, lighting = {}, sounds = {}, tracers = {}, nohands = {} }
        S.swaps = {}
        local section = "skins"
        for _, line in ipairs(S.lines) do
            local h = header(line)
            if h then
                section = h
            elseif section == "skins" and not line:match("^%s*%-%-") and swapLine(line) then
                local w, owned, target = swapLine(line)
                S.swaps[w] = S.swaps[w] or {}
                S.swaps[w][owned] = target
            else
                local k, v = pair(line)
                if k then
                    S.values[section] = S.values[section] or {}
                    S.values[section][k] = v
                end
            end
        end
    end
    local function configText()
        if #S.lines == 0 then return "-- Rivals config\n" end
        return table.concat(S.lines, "\n") .. "\n"
    end
    local function markChanged()
        S.dirty = configText() ~= S.cleanText
        S.status = S.dirty and ("Saved to " .. LOLCAT_SKIN_FILE) or "No changes."
    end
    local function configClashes()
        local out, section, touched, used, swaps = {}, "skins", {}, {}, {}
        for _, line in ipairs(S.lines) do
            local h = header(line)
            if h then
                section = h
            elseif section == "skins" then
                local w, o, t = swapLine(line)
                if w then
                    swaps[#swaps + 1] = { o, t }
                else
                    local k, v = pair(line)
                    local low = v and v:lower()
                    if k and v and low ~= "default" and low ~= "standard" then
                        if touched[v] or touched[k] then out[#out + 1] = k .. " -> " .. v else touched[v], touched[k] = true, true end
                    end
                end
            elseif section == "finishers" or section == "charms" then
                local k, v = pair(line)
                if k and v then
                    local model = section == "charms" and (v:match("^(Season %d+)%s") or v) or v
                    used[section] = used[section] or {}
                    local u = used[section]
                    if u[k] or u[model] then out[#out + 1] = k .. " -> " .. v else u[k], u[model] = true, true end
                end
            end
        end
        for _, sw in ipairs(swaps) do
            if touched[sw[2]] or touched[sw[1]] then out[#out + 1] = sw[1] .. " -> " .. sw[2] else touched[sw[2]], touched[sw[1]] = true, true end
        end
        return out
    end
    local function saveConfig()
        local content = configText()
        -- 1. Mirror to rivals_config.lua and workspace/rivals_config.lua for compatibility with in-game swappers
        pcall(function()
            writefile(FILE, content)
            writefile("workspace/" .. FILE, content)
            S.baseline = content
        end)
        -- 2. Save dedicated Lolcatskinchanger.lua (Lua table format)
        pcall(function()
            local luaLines = {
                "-- Lolcat Skinchanger Configuration",
                "-- Automatically saved by Lolcat UI",
                "return {",
                "    Skins = {"
            }
            if S.values.skins then
                for w, sk in pairs(S.values.skins) do
                    if type(w) == "string" and type(sk) == "string" and not sk:match("^%s*%{") and not w:match("^%s*%{") then
                        table.insert(luaLines, string.format("        [%q] = %q,", w, sk))
                    end
                end
            end
            table.insert(luaLines, "    },")
            table.insert(luaLines, "    Swaps = {")
            if S.swaps then
                for w, sws in pairs(S.swaps) do
                    table.insert(luaLines, string.format("        [%q] = {", w))
                    for o, t in pairs(sws) do
                        table.insert(luaLines, string.format("            [%q] = %q,", o, t))
                    end
                    table.insert(luaLines, "        },")
                end
            end
            table.insert(luaLines, "    },")
            for _, sec in ipairs({ "wraps", "finishers", "charms", "skybox", "lighting", "sounds", "tracers", "nohands" }) do
                table.insert(luaLines, "    " .. sec:sub(1,1):upper() .. sec:sub(2) .. " = {")
                if S.values[sec] then
                    for k, v in pairs(S.values[sec]) do
                        table.insert(luaLines, string.format("        [%q] = %q,", k, v))
                    end
                end
                table.insert(luaLines, "    },")
            end
            table.insert(luaLines, "}")
            writefile(LOLCAT_SKIN_FILE, table.concat(luaLines, "\n"))
        end)
        -- 3. Save dedicated Lolcatskinchanger.json
        pcall(function()
            local t = {
                skins = S.values.skins or {},
                swaps = S.swaps or {},
                wraps = S.values.wraps or {},
                finishers = S.values.finishers or {},
                charms = S.values.charms or {},
                skybox = S.values.skybox or {},
                lighting = S.values.lighting or {},
                sounds = S.values.sounds or {},
                tracers = S.values.tracers or {},
                nohands = S.values.nohands or {},
            }
            writefile(LOLCAT_SKIN_JSON, HttpService:JSONEncode(t))
        end)
        S.cleanText, S.dirty = content, false
        S.status = "Saved to " .. LOLCAT_SKIN_FILE
    end

    function SC.loadConfig()
        local raw = nil
        -- Check Lolcatskinchanger.lua first, then Lolcatskinchanger.json, then rivals_config.lua
        if isfile(LOLCAT_SKIN_FILE) then
            local ok, txt = pcall(readfile, LOLCAT_SKIN_FILE)
            if ok and type(txt) == "string" and #txt > 10 then
                local fn = loadstring(txt)
                if type(fn) == "function" then
                    local okExec, res = pcall(fn)
                    if okExec and type(res) == "table" then
                        local lines = { "-- Rivals config", "[Skins]" }
                        if res.Skins then
                            for w, sk in pairs(res.Skins) do
                                if type(w) == "string" and type(sk) == "string" and not sk:match("^%s*%{") and not w:match("^%s*%{") then
                                    table.insert(lines, w .. "=" .. sk)
                                end
                            end
                        end
                        if res.Swaps then
                            for w, sws in pairs(res.Swaps) do
                                for o, t in pairs(sws) do table.insert(lines, w .. " | " .. o .. " > " .. t) end
                            end
                        end
                        for _, sec in ipairs({ "Wraps", "Finishers", "Charms", "Skybox", "Lighting", "Sounds", "Tracers", "NoHands" }) do
                            local stbl = res[sec]
                            if stbl and next(stbl) then
                                table.insert(lines, "")
                                table.insert(lines, "[" .. sec .. "]")
                                for k, v in pairs(stbl) do table.insert(lines, k .. "=" .. v) end
                            end
                        end
                        raw = table.concat(lines, "\n")
                    end
                end
                if not raw then raw = txt end
            end
        end
        if not raw and isfile(LOLCAT_SKIN_JSON) then
            local ok, txt = pcall(readfile, LOLCAT_SKIN_JSON)
            if ok and type(txt) == "string" and #txt > 10 then
                local okDec, res = pcall(function() return HttpService:JSONDecode(txt) end)
                if okDec and type(res) == "table" then
                    local lines = { "-- Rivals config", "[Skins]" }
                    if res.skins then
                        for w, sk in pairs(res.skins) do
                            if type(w) == "string" and type(sk) == "string" and not sk:match("^%s*%{") and not w:match("^%s*%{") then
                                table.insert(lines, w .. "=" .. sk)
                            end
                        end
                    end
                    if res.swaps then
                        for w, sws in pairs(res.swaps) do
                            for o, t in pairs(sws) do table.insert(lines, w .. " | " .. o .. " > " .. t) end
                        end
                    end
                    for _, sec in ipairs({ "wraps", "finishers", "charms", "skybox", "lighting", "sounds", "tracers", "nohands" }) do
                        local stbl = res[sec]
                        if stbl and next(stbl) then
                            table.insert(lines, "")
                            table.insert(lines, "[" .. sec:sub(1,1):upper() .. sec:sub(2) .. "]")
                            for k, v in pairs(stbl) do table.insert(lines, k .. "=" .. v) end
                        end
                    end
                    raw = table.concat(lines, "\n")
                end
            end
        end
        if not raw and isfile(FILE) then
            raw = readfile(FILE)
        end

        local content = (raw or ""):gsub("\r\n", "\n"):gsub("\r", "\n")
        if content:sub(1, 3) == string.char(239, 187, 191) then content = content:sub(4) end
        local lines = {}
        for line in (content .. "\n"):gmatch("(.-)\n") do lines[#lines + 1] = line end
        while lines[#lines] == "" do table.remove(lines) end
        local cleaned = {}
        for _, line in ipairs(lines) do
            local k, v = pair(line)
            if not (k and v and k == v) then cleaned[#cleaned + 1] = line end
        end
        S.lines, S.baseline = cleaned, raw
        indexConfig()
        S.readable = true
        S.cleanText, S.dirty = configText(), false
        local bad = configClashes()
        S.status = #bad > 0 and ("Two lines use the same item - skipped: " .. table.concat(bad, ", "))
            or (raw and "Loaded skinchanger config." or "Nothing saved yet - pick something.")
    end

    local autoApplyTimer = nil
    function SC.triggerAutoApply()
        if not SC.autoApply then return end
        if autoApplyTimer then return end
        autoApplyTimer = task.delay(0.2, function()
            autoApplyTimer = nil
            if SC.apply then pcall(SC.apply) end
        end)
    end

    local function setMapping(section, key, value)
        if S.busy or not S.readable then return end
        local output, current, found = {}, "skins", false
        for _, line in ipairs(S.lines) do
            local h = header(line)
            if h then current = h end
            local k = (not h) and pair(line) or nil
            if current == section and k == key then
                if not found and value then output[#output + 1] = key .. "=" .. value end
                found = true
            else
                output[#output + 1] = line
            end
        end
        if not found and value then
            local position = section == "skins" and 1 or nil
            current = "skins"
            for i, line in ipairs(output) do
                local h = header(line)
                if h then current = h end
                if current == section then position = i + 1 end
            end
            if not position then
                output[#output + 1] = ""
                output[#output + 1] = "[" .. section:sub(1, 1):upper() .. section:sub(2) .. "]"
                position = #output + 1
            end
            table.insert(output, position, key .. "=" .. value)
        end
        S.lines = output
        indexConfig()
        markChanged()
        saveConfig()
        SC.triggerAutoApply()
    end

    local function setSwap(weapon, owned, target)
        if S.busy or not S.readable then return end
        local output, section, lastSkin = {}, "skins", 0
        for _, line in ipairs(S.lines) do
            local h = header(line)
            if h then section = h end
            local keep = true
            if section == "skins" and not h then
                local w, o = swapLine(line)
                if w == weapon and o == owned then keep = false end
            end
            if keep then
                output[#output + 1] = line
                if section == "skins" and not h then lastSkin = #output end
            end
        end
        if target then table.insert(output, lastSkin + 1, weapon .. " | " .. owned .. " > " .. target) end
        S.lines = output
        indexConfig()
        markChanged()
        saveConfig()
        SC.triggerAutoApply()
    end
    SC.setMapping, SC.setSwap = setMapping, setSwap

    local function guarded(change, target)
        local before, was = S.lines, #configClashes()
        change()
        if #configClashes() > was then
            S.lines = before
            indexConfig()
            markChanged()
            S.status = target .. " is already used by another line - change that line first."
        end
    end

    -- what you own (CosmeticInventory read from the game's Lua tables) ---------------
    local inventory = nil
    do
        local mrd = memory_read
        local function rd(a) local ok, v = pcall(mrd, "uintptr_t", a) return ok and v or nil end
        local function rint(a) local ok, v = pcall(mrd, "int", a) return ok and v or nil end
        local function rbyte(a) local ok, v = pcall(mrd, "byte", a) return ok and v or nil end
        local TAG_TABLE, TAG_THREAD = 7, 10
        local function isTable(t) return t and t > 0x10000 and rbyte(t + 1) == TAG_TABLE end
        local function moduleTable(ms)
            local thread = ms and ms.Address and rd(ms.Address + 0x170)
            if not thread or thread < 0x10000 or rbyte(thread + 1) ~= TAG_THREAD then return nil end
            local g = rd(thread + 0x68)
            local reg = g and g > 0x10000 and rd(g + 0x620)
            if not isTable(reg) then return nil end
            local slot, size, arr = rint(ms.Address + 0x178), rint(reg + 8), rd(reg + 0x20)
            if not slot or not size or not arr or slot < 1 or slot > size then return nil end
            local t = rd(arr + (slot - 1) * 16)
            return isTable(t) and t or nil
        end
        local function fields(t)
            local out = {}
            if not isTable(t) then return out end
            local base, l = rd(t + 0x18), rbyte(t + 4)
            if not base or base < 0x10000 or not l or l > 16 then return out end
            for i = 0, 2 ^ l - 1 do
                local node = base + i * 32
                local tt, kp = rint(node + 12), rd(node + 16)
                if tt and tt ~= 0 and kp and kp > 0x10000 then
                    local ok, key = pcall(mrd, "string", kp + 24)
                    if ok and type(key) == "string" and #key > 0 and #key < 80 then out[key] = { rd(node), tt } end
                end
            end
            return out
        end
        function SC.readInventory()
            if not hasMem then inventory = nil return false end
            local ok, result = pcall(function()
                local ps = LocalPlayer.PlayerScripts
                local ctl = moduleTable(ps.Controllers.PlayerDataController)
                local cur = ctl and fields(ctl).CurrentData
                local data = cur and fields(cur[1]).Data
                local inv = data and fields(data[1]).CosmeticInventory
                if not inv or not isTable(inv[1]) then return nil end
                local out, n = {}, 0
                for name, v in pairs(fields(inv[1])) do
                    n = n + 1
                    if v[2] == TAG_TABLE then
                        local on = {}
                        for weapon in pairs(fields(v[1])) do on[weapon] = true end
                        out[name] = on
                    else
                        out[name] = true
                    end
                end
                return n > 0 and out or nil
            end)
            inventory = ok and result or nil
            return inventory ~= nil
        end
    end
    local function owns(name, weapon)
        local e = inventory and inventory[name]
        if e == true then return true end
        if type(e) ~= "table" then return false end
        return weapon == nil or e.IsUniversal == true or e[weapon] == true
    end
    function SC.invStatus() return inventory and "inventory read" or "inventory not readable (lists show everything)" end

    -- catalogue: weapons, wraps, finishers, charms, skies ---------------------------------
    local WEAPON_SLOTS = {}
    for slot, names in pairs({
        Primary = { "Assault Rifle", "Bow", "Burst Rifle", "Crossbow", "Distortion", "Energy Rifle", "Flamethrower",
            "Grenade Launcher", "Gunblade", "Minigun", "Paintball Gun", "Permafrost", "RPG", "Shotgun", "Sniper", "Wildcat" },
        Secondary = { "Daggers", "Energy Pistols", "Exogun", "Flare Gun", "Handgun", "Revolver", "Shorty", "Slingshot",
            "Spray", "Uzi", "Warper" },
        Melee = { "Battle Axe", "Chainsaw", "Fists", "Katana", "Knife", "Maul", "Riot Shield", "Scythe", "Spear", "Trowel" },
        Utility = { "Flashbang", "Freeze Ray", "Grappler", "Grenade", "Jump Pad", "Medkit", "Molotov", "Satchel",
            "Smoke Grenade", "Subspace Tripmine", "War Horn", "Warpstone" },
    }) do
        for _, name in ipairs(names) do WEAPON_SLOTS[name] = slot end
    end
    local WRAP_RARITY = { "Common", "Rare", "Legendary", "Mythical", "Unique", "Genuine", "Unobtainable" }
    local RARITY_COLORS = {
        Common = pack(123, 255, 0), Rare = pack(0, 221, 255), Legendary = pack(255, 60, 60),
        Mythical = pack(129, 133, 242), Unique = pack(255, 140, 0), Genuine = pack(127, 163, 90),
    }
    local RANKS = { "Archnemesis", "Nemesis", "Onyx 3", "Onyx 2", "Onyx 1", "Diamond 3", "Diamond 2", "Diamond 1",
        "Platinum 3", "Platinum 2", "Platinum 1", "Gold 3", "Gold 2", "Gold 1", "Silver 3", "Silver 2", "Silver 1",
        "Bronze 3", "Bronze 2", "Bronze 1", "Unranked" }
    local SKY_FACES = {
        blue = "14147882761", space = "10196550367", graveyard = "135908632589654",
        ["sudden death"] = "84214501374682", station = "2108482231", westown = "12261809766",
    }

    local BUILTIN_WRAPS = {
        { "Gold", "Legendary" }, { "Diamond", "Mythical" }, { "Damascus", "Legendary" },
        { "Obsidian", "Mythical" }, { "Void", "Mythical" }, { "Rainbow", "Legendary" },
        { "Glitch", "Rare" }, { "Cyber", "Rare" }, { "Neon", "Rare" }, { "Comic", "Rare" },
        { "Pixel", "Common" }, { "Lava", "Legendary" }, { "Ice", "Rare" }, { "Galaxy", "Mythical" },
        { "Cherry Blossom", "Rare" }, { "Carbon Fiber", "Common" }, { "Dragon Scale", "Legendary" },
        { "Toxic Waste", "Rare" }, { "Blood Splatter", "Rare" }, { "Retro Wave", "Rare" },
        { "Matrix", "Legendary" }, { "Holographic", "Legendary" }, { "Amethyst", "Rare" },
        { "Ruby", "Rare" }, { "Emerald", "Rare" }, { "Sapphire", "Rare" }, { "Tiger Stripe", "Common" },
        { "Zebra", "Common" }, { "Snow Camo", "Common" }, { "Desert Camo", "Common" },
        { "Urban Camo", "Common" }, { "Flame", "Rare" }, { "Lightning", "Rare" },
        { "Candy Cane", "Common" }, { "Gingerbread", "Common" }, { "Halloween Pumpkin", "Rare" },
        { "Midnight", "Rare" }, { "Vaporwave", "Rare" }, { "Nebula", "Mythical" }, { "Sunburst", "Rare" },
    }

    local BUILTIN_FINISHERS = {
        { "Black Hole", "Mythical" }, { "Lightning Strike", "Legendary" }, { "Nuke", "Mythical" },
        { "Ghost", "Rare" }, { "Confetti", "Common" }, { "Shatter", "Rare" }, { "Vaporize", "Legendary" },
        { "Tombstone", "Rare" }, { "Meteor", "Mythical" }, { "Disintegration", "Legendary" },
        { "Fireworks", "Rare" }, { "Pixelate", "Rare" }, { "Golden Statue", "Legendary" },
        { "Ascension", "Mythical" }, { "Abduction", "Mythical" }, { "Frost Freeze", "Legendary" },
        { "Lava Eruption", "Legendary" }, { "Hammer Smash", "Rare" }, { "Slash Cut", "Rare" },
        { "Shadow Realm", "Mythical" },
    }

    local BUILTIN_CHARMS = {
        { "Season 1 Archnemesis", "Mythical" }, { "Season 1 Nemesis", "Mythical" }, { "Season 1 Onyx", "Legendary" },
        { "Season 1 Diamond", "Legendary" }, { "Season 1 Platinum", "Rare" }, { "Season 1 Gold", "Rare" },
        { "Season 1 Silver", "Common" }, { "Season 1 Bronze", "Common" },
        { "Season 2 Archnemesis", "Mythical" }, { "Season 2 Nemesis", "Mythical" }, { "Season 2 Onyx", "Legendary" },
        { "Season 2 Diamond", "Legendary" }, { "Season 2 Platinum", "Rare" }, { "Season 2 Gold", "Rare" },
        { "Season 2 Silver", "Common" }, { "Season 2 Bronze", "Common" },
        { "Season 3 Archnemesis", "Mythical" }, { "Season 3 Nemesis", "Mythical" }, { "Season 3 Onyx", "Legendary" },
        { "Season 3 Diamond", "Legendary" }, { "Season 3 Platinum", "Rare" }, { "Season 3 Gold", "Rare" },
        { "Cat", "Common" }, { "Dog", "Common" }, { "Duck", "Common" }, { "Skull", "Rare" },
        { "Dice", "Common" }, { "Heart", "Common" }, { "Star", "Rare" }, { "Crown", "Legendary" },
        { "Ghost", "Rare" }, { "Bomb", "Rare" }, { "Coin", "Common" }, { "Diamond", "Legendary" },
        { "Trophy", "Legendary" }, { "Target", "Common" }, { "Controller", "Rare" },
        { "Flame", "Rare" }, { "Lightning", "Rare" }, { "8-Ball", "Common" }, { "Pizza", "Common" },
    }

    function SC.loadCatalog()
        pcall(SC.readInventory)
        local out = { weapons = {}, wraps = {}, finishers = {}, charms = {}, skyFull = {}, skyFace = {}, loaded = true }
        local byName = {}

        -- Load skin_icon_map.json (disk cache first, then CDN)
        local mapJson = nil
        local mapFile = CACHE .. "/skin_icon_map.json"
        if isfile and isfile(mapFile) then
            local okR, txt = pcall(readfile, mapFile)
            if okR and type(txt) == "string" and #txt > 100 then mapJson = txt end
        end
        if not mapJson then
            local okH, txt = pcall(httpget, SITE .. "skin_icon_map.json")
            if (not okH or not txt or #txt < 100) and game and game.HttpGet then
                okH, txt = pcall(function() return game:HttpGet(SITE .. "skin_icon_map.json") end)
            end
            if okH and type(txt) == "string" and #txt > 100 then
                mapJson = txt
                pcall(makefolder, CACHE)
                pcall(writefile, mapFile, txt)
            end
        end

        local iconMap = nil
        if mapJson then
            pcall(function() iconMap = HttpService:JSONDecode(mapJson) end)
        end

        if type(iconMap) == "table" then
            for wName, skins in pairs(iconMap) do
                local entry = byName[wName]
                if not entry then
                    entry = { name = wName, slot = WEAPON_SLOTS[wName] or "Other", skins = {}, info = {} }
                    byName[wName] = entry
                end
                if type(skins) == "table" then
                    if skins["Standard"] and skins["Standard"].src then
                        entry.icon = skins["Standard"].src
                    end
                    for sName, sData in pairs(skins) do
                        if sName ~= "Standard" and sName ~= "Default" then
                            entry.skins[#entry.skins + 1] = sName
                            entry.info[sName] = {
                                src = type(sData) == "table" and sData.src or nil,
                                rarity = type(sData) == "table" and sData.rarity or "Rare"
                            }
                        end
                    end
                end
            end
        end

        local uniSkins = { "Gold", "Diamond", "Damascus", "Obsidian", "Void", "Rainbow", "Glitch", "Cyber", "Neon", "Comic", "Pixel", "Lava", "Ice", "Galaxy", "Cherry Blossom", "Carbon Fiber", "Toxic", "Bones", "Dragon", "Valkyrie" }
        local specSkins = {
            Katana = { "Oni", "Blood", "Midnight", "Demon" },
            Knife = { "Fade", "Tiger", "Crimson" },
            Scythe = { "Grim", "Reaping", "Soul", "Shadow" },
            Sniper = { "Retro", "Hyperbeast", "Midnight" },
            ["Assault Rifle"] = { "Hyperbeast", "Tactical", "Hazard" },
            Shotgun = { "Rust", "Sawed-Off", "Enforcer" },
            Minigun = { "Heavy Metal", "Industrial" },
            RPG = { "Nuke", "Shark", "Hazard" },
            Bow = { "Elven", "Flame", "Frost" },
            Crossbow = { "Hunter", "Toxic" },
            Flamethrower = { "Inferno", "Hazard" },
            ["Paintball Gun"] = { "Splatter", "Graffiti" },
            Permafrost = { "Glacier", "Blizzard", "Crystal" },
            Revolver = { "Cowboy", "Sheriff", "Outlaw", "Chrome" },
            Uzi = { "Gangster", "Chrome", "Speed" },
            ["Battle Axe"] = { "Viking", "Barbarian", "Executioner" },
            Chainsaw = { "Doom", "Lumberjack" },
            Fists = { "Brass Knuckles", "Boxing" },
            Maul = { "Warhammer", "Titan", "Breaker" },
            ["Riot Shield"] = { "Police", "SWAT", "Bulwark" },
            Spear = { "Spartan", "Gladiator", "Tribal" },
            Trowel = { "Builder", "Golden Brick" },
        }

        for name, slot in pairs(WEAPON_SLOTS) do
            local entry = byName[name]
            if not entry then
                entry = { name = name, slot = slot, skins = {}, info = {} }
                byName[name] = entry
            end
            local seen = {}
            for _, s in ipairs(entry.skins) do seen[s] = true end
            for _, s in ipairs(uniSkins) do
                if not seen[s] then
                    entry.skins[#entry.skins + 1] = s
                    seen[s] = true
                    entry.info[s] = entry.info[s] or { rarity = (s == "Diamond" or s == "Obsidian" or s == "Void" or s == "Galaxy") and "Mythical" or "Legendary" }
                end
            end
            if specSkins[name] then
                for _, s in ipairs(specSkins[name]) do
                    if not seen[s] then
                        entry.skins[#entry.skins + 1] = s
                        seen[s] = true
                        entry.info[s] = entry.info[s] or { rarity = "Rare" }
                    end
                end
            end
            table.sort(entry.skins)
        end

        pcall(function()
            local weapons = LocalPlayer.PlayerScripts.Assets.ViewModels.Weapons
            for _, w in ipairs(weapons:GetChildren()) do
                if w.Name ~= "Unobtainable" then
                    local entry = byName[w.Name]
                    if not entry then
                        entry = { name = w.Name, slot = WEAPON_SLOTS[w.Name] or "Other", skins = {}, info = {} }
                        byName[w.Name] = entry
                    end
                    local seen = {}
                    for _, s in ipairs(entry.skins) do seen[s] = true end
                    for _, child in ipairs(w:GetChildren()) do
                        local cn = child.Name
                        if cn ~= "Hitbox" and cn ~= "Sound" and cn ~= "Script" and cn ~= "Standard" and cn ~= "Default" then
                            if not seen[cn] then
                                entry.skins[#entry.skins + 1] = cn
                                seen[cn] = true
                                entry.info[cn] = entry.info[cn] or { rarity = "Rare" }
                            end
                        end
                    end
                    table.sort(entry.skins)
                end
            end
        end)

        for _, w in pairs(byName) do out.weapons[#out.weapons + 1] = w end
        table.sort(out.weapons, function(a, b) return a.name < b.name end)

        for _, row in ipairs(BUILTIN_WRAPS) do
            out.wraps[#out.wraps + 1] = { name = row[1], rarity = row[2] }
        end
        pcall(function()
            local folder = LocalPlayer.PlayerScripts.Assets.Wraps
            for _, m in ipairs(folder:GetChildren()) do
                local found = false
                for _, w in ipairs(out.wraps) do if w.name == m.Name then found = true break end end
                if not found then out.wraps[#out.wraps + 1] = { name = m.Name, rarity = "Rare" } end
            end
        end)
        table.sort(out.wraps, function(a, b) return a.name < b.name end)

        for _, row in ipairs(BUILTIN_FINISHERS) do
            out.finishers[#out.finishers + 1] = { name = row[1], rarity = row[2] }
        end
        pcall(function()
            local folder = game:GetService("ReplicatedStorage").Modules.Finishers
            for _, m in ipairs(folder:GetChildren()) do
                local found = false
                for _, f in ipairs(out.finishers) do if f.name == m.Name then found = true break end end
                if not found then out.finishers[#out.finishers + 1] = { name = m.Name, rarity = "Rare" } end
            end
        end)
        table.sort(out.finishers, function(a, b) return a.name < b.name end)

        for _, row in ipairs(BUILTIN_CHARMS) do
            out.charms[#out.charms + 1] = { name = row[1], rarity = row[2] }
        end
        pcall(function()
            local folder = LocalPlayer.PlayerScripts.Assets.Charms
            for _, m in ipairs(folder:GetChildren()) do
                local found = false
                for _, c in ipairs(out.charms) do if c.name == m.Name then found = true break end end
                if not found then out.charms[#out.charms + 1] = { name = m.Name, rarity = "Rare" } end
            end
        end)
        table.sort(out.charms, function(a, b) return a.name < b.name end)

        for name, face in pairs(SKY_FACES) do out.skyFace[name] = face end

        S.cat = out
        S.status = string.format("%d weapons, %d wraps, %d finishers, %d charms (Ready)", #out.weapons, #out.wraps, #out.finishers, #out.charms)
    end

    -- run the changer -------------------------------------------------------------------
    local function currentContext()
        local ok, result = pcall(function()
            if tonumber(game.GameId) ~= RIVALS_GAME_ID or not game:IsLoaded() then return nil end
            local jobId = game.JobId
            if type(jobId) ~= "string" or jobId == "" then return nil end
            local weapons = LocalPlayer.PlayerScripts.Assets.ViewModels.Weapons
            if not weapons or not weapons.Address or #weapons:GetChildren() == 0 then return nil end
            return { key = jobId .. ":" .. tostring(weapons.Address), wf = weapons.Address }
        end)
        return ok and result or nil
    end
    local function upstreamBusy()
        local stamp = _G.__RIVALS_SKIN_CHANGER_BUSY
        return type(stamp) == "number" and tick() - stamp < 180
    end
    local function changerSource()
        for _, p in ipairs(SCRIPT_FILES) do
            local ok, exists = pcall(isfile, p)
            if ok and exists then
                local okR, body = pcall(readfile, p)
                if okR and type(body) == "string" and #body > 50 and not body:find("^%s*loadstring") then
                    return body, p
                end
            end
        end
        local swapperCache = "lolcat_imgcache/swapper.lua"
        if isfile and isfile(swapperCache) then
            local okR, body = pcall(readfile, swapperCache)
            if okR and type(body) == "string" and #body > 500 then return body, swapperCache end
        end
        local SWAPPER_URL = "https://raw.githubusercontent.com/Martinikaws/RivalsSkinChangerSITEBASED/refs/heads/main/main.lua"
        local okH, remote = pcall(httpget, SWAPPER_URL)
        if (not okH or not remote or #remote < 500) and game and game.HttpGet then
            okH, remote = pcall(function() return game:HttpGet(SWAPPER_URL) end)
        end
        if okH and type(remote) == "string" and #remote > 500 then
            pcall(makefolder, "lolcat_imgcache")
            pcall(writefile, swapperCache, remote)
            return remote, "remote"
        end
        return nil, nil
    end

    local function apply()
        saveConfig()
        local source, from = changerSource()
        if not source then
            S.status = "Saved to " .. LOLCAT_SKIN_FILE .. ". Swapper script not found."
            return
        end
        _G.__RIVALS_SKIN_CHANGER_BUSY = nil
        S.status = "Applying skins in-game..."
        local fn, err = loadstring(source)
        if type(fn) ~= "function" then
            S.status = "Saved to " .. LOLCAT_SKIN_FILE .. " (compile error: " .. tostring(err):sub(1, 40) .. ")"
            return
        end
        task.spawn(function()
            local okRun, runErr = pcall(fn)
            if okRun then
                S.status = "Applied skins! Saved to " .. LOLCAT_SKIN_FILE
                if typeof(notify) == "function" then
                    pcall(notify, "Skins applied! Saved to " .. LOLCAT_SKIN_FILE, "Skin Changer", 4)
                end
            else
                S.status = "Applied (Saved to " .. LOLCAT_SKIN_FILE .. ")"
            end
        end)
    end
    function SC.job(label, fn)
        if S.busy then return end
        S.busy, S.status = true, label
        task.spawn(function()
            local ok, err = pcall(fn)
            S.busy = false
            if not ok then S.status = "Error: " .. tostring(err):gsub("^.-:%d+: ", ""):sub(1, 90) end
        end)
    end
    SC.apply = apply

    ----------------------------------------------------------------------
    -- tile grid + skin pages
    ----------------------------------------------------------------------
    local TW, TH = 104, 120
    local function tiles(id, x, y, w, h, items, isSel, dt, badge)
        local cols = max(1, floor((w + 8) / (TW + 8)))
        local rows = ceil(#items / cols)
        local off = cscroll(id, x, y, w, h, rows * (TH + 8), dt)
        local gap = cols > 1 and (w - cols * TW) / (cols - 1) or 0
        local picked
        local first = floor(off / (TH + 8))
        for r = first, min(rows - 1, first + ceil(h / (TH + 8))) do
            for c = 0, cols - 1 do
                local it = items[r * cols + c + 1]
                if it then
                    local tx, ty = x + c * (TW + gap), y + r * (TH + 8) - off
                    local sel = isSel(it)
                    local hot = live(tx, ty, TW, TH)
                    R.rect(tx - 1, ty - 1, TW + 2, TH + 2, sel and T.Accent or T.Outline, 6)
                    R.rect(tx, ty, TW, TH, hot and T.GradientTop or T.GradientMid, 5)
                    local isz = TW - 28
                    local ix, iy = tx + 14, ty + 8
                    if it.none then
                        R.circle(tx + TW / 2, iy + isz / 2, 18, T.Unselected, false, 2, 24)
                        R.line(tx + TW / 2 - 12, iy + isz / 2 + 12, tx + TW / 2 + 12, iy + isz / 2 - 12, T.Unselected, 2)
                    elseif it.color then
                        R.rect(ix, iy, isz, isz, it.color, 4)
                    else
                        local data = imageData(it.src)
                        if data and R.image(it.src, data, ix, iy, isz, isz) then
                            -- image drawn
                        else
                            R.rect(ix, iy, isz, isz, T.TabButtonSelected or T.GradientTop, 4)
                            local badgeCol = it.rarity and RARITY_COLORS[it.rarity] or T.Accent
                            R.rect(ix + 6, iy + 6, isz - 12, 3, badgeCol, 1)
                            local initial = (it.name:match("(%u%l*)") or it.name:sub(1, 4)):upper()
                            R.text(ix + (isz - R.tw(initial, 13)) / 2, iy + (isz - 13) / 2, initial, 13, T.TextColor, true)
                        end
                    end
                    local nm = fit(it.name, TW - 10, 12)
                    R.text(tx + (TW - R.tw(nm, 12)) / 2, ty + TH - 30, nm, 12, sel and T.TextColor or T.Unselected, sel)
                    local rc = it.rarity and RARITY_COLORS[it.rarity]
                    if rc then R.rect(tx + 30, ty + TH - 6, TW - 60, 2, rc, 1) end
                    local mark = badge and badge(it)
                    if mark then
                        R.rect(tx + TW - 24, ty + 6, 18, 18, T.Accent, 9)
                        R.text(tx + TW - 15 - R.tw(mark, 12) / 2, ty + 8, mark, 12, pack(8, 10, 10), true)
                    end
                    if click(tx, ty, TW, TH) then picked = it end
                end
            end
        end
        if #items == 0 then R.text(x + 4, y + 6, "Nothing matches.", 13, T.Unselected, false) end
        return picked
    end
    local function sideList(id, x, y, w, h, names, selected, marked, dt)
        local rowH = 28
        local off = cscroll(id, x, y, w, h, #names * rowH, dt)
        local picked
        for i = max(1, floor(off / rowH)), min(#names, ceil((off + h) / rowH) + 1) do
            local n = names[i]
            local ry = y + (i - 1) * rowH - off
            local hot = live(x, ry, w, rowH - 3)
            if n == selected then R.rect(x, ry, w, rowH - 3, T.TabButtonSelected, 4); R.rect(x, ry + 5, 2, rowH - 13, T.Accent, 1)
            elseif hot then R.rect(x, ry, w, rowH - 3, T.GradientTop, 4) end
            R.text(x + 10, ry + 6, fit(n, w - 30, 13), 13, n == selected and T.Accent or T.TextColor, n == selected)
            if marked and marked(n) then R.circle(x + w - 11, ry + (rowH - 3) / 2, 3, T.Accent, true, 1, 12) end
            if click(x, ry, w, rowH - 3) then picked = n end
        end
        return picked
    end
    local function weaponEntry(name)
        for _, w in ipairs(S.cat.weapons) do if w.name == name then return w end end
    end
    local function swapCount(weapon)
        local n = 0
        for _ in pairs(S.swaps[weapon] or {}) do n = n + 1 end
        return n
    end
    SC.ownedOnly = true
    local function ownedOnly() return SC.ownedOnly and inventory ~= nil end
    local function skinItems(w, exclude, q, withNone, ownedFor)
        local out = {}
        if withNone then out[1] = { name = "None", none = true } end
        local mine = ownedFor and ownedOnly()
        for _, skin in ipairs(w and w.skins or {}) do
            if skin ~= exclude and matches(q, skin) and (not mine or owns(skin, ownedFor) or (S.swaps[ownedFor] or {})[skin] ~= nil) then
                local info = w.info[skin] or {}
                out[#out + 1] = { name = skin, src = info.src, rarity = info.rarity }
            end
        end
        return out
    end

    -- footer shared by every skin page: status + reload + Save & Apply
    local function footer(x, y, w, h)
        local fy = y + h - 34
        R.rect(x, fy - 6, w, 1, T.Outline)
        local st = (S.busy and "Working...  " or "") .. tostring(S.status)
        R.text(x + 2, fy + 8, fit(st, w - 330, 13), 13, S.dirty and T.TextColor or T.Unselected, false)
        if btn(x + w - 300, fy, 110, 28, "Reload") then SC.job("Reading config...", function() SC.loadConfig() SC.loadCatalog() end) end
        if btn(x + w - 180, fy, 170, 28, "Save & Apply", true, S.busy) then SC.job("Applying...", apply) end
    end

    local SLOT_ORDER = { "Primary", "Secondary", "Melee", "Utility", "Other" }
    SC.view, SC.slotTab, SC.mode, SC.swapStep, SC.weapon, SC.swapOwned = "main", "All", "Switch", 1, nil, {}
    local function hdrBack(x, y, wpn, sub)
        if btn(x, y, 78, 30, "< Back") then SC.view = "main"; TI.focus = nil end
        local data = imageData(wpn.icon)
        if not (data and R.image(wpn.icon, data, x + 90, y - 4, 38, 38)) then
            R.rect(x + 90, y - 4, 38, 38, T.GradientMid, 5)
            local initial = (wpn.name:match("(%u%l*)") or wpn.name:sub(1, 3)):upper()
            R.text(x + 90 + (38 - R.tw(initial, 12)) / 2, y + 8, initial, 12, T.Accent, true)
        end
        R.text(x + 138, y, wpn.name, 16, T.TextColor, true)
        R.text(x + 138, y + 20, sub, 12, T.Unselected, false)
    end

    function SC.drawWeapons(x, y, w, h, dt)
        footer(x, y, w, h)
        h = h - 42
        if R.clip then R.clip = { R.clip[1], R.clip[2], R.clip[3], y + h } end
        if not S.cat.loaded then R.text(x + 4, y + 8, "Loading lists...", 14, T.Unselected, false) return end
        local wpn = SC.view == "weapon" and weaponEntry(SC.weapon)
        if not wpn then SC.view = "main" end
        if SC.view == "main" then
            local tabs = { "All" }
            for _, slot in ipairs(SLOT_ORDER) do
                for _, wp in ipairs(S.cat.weapons) do if (wp.slot or "Other") == slot then tabs[#tabs + 1] = slot break end end
            end
            local ti = 1
            for i, t in ipairs(tabs) do if t == SC.slotTab then ti = i end end
            local pk = seg(x, y, min(430, w - 260), 30, tabs, ti)
            if pk then SC.slotTab = tabs[pk]; resetScroll("wmain") end
            local q = tbox("wsearch", x + w - 240, y, 228, 30, "Search weapons or skins...")
            local only = SC.slotTab ~= "All" and SC.slotTab or nil
            local gx, gy, gw, gh = x, y + 42, w - 14, h - 42
            local cols = max(1, floor((gw + 8) / (TW + 8)))
            local gap = cols > 1 and (gw - cols * TW) / (cols - 1) or 0
            local rows = {}
            for _, slot in ipairs(only and { only } or SLOT_ORDER) do
                local list = {}
                for _, wp in ipairs(S.cat.weapons) do
                    if (wp.slot or "Other") == slot then
                        local hit = matches(q, wp.name)
                        if not hit then for _, sk in ipairs(wp.skins) do if matches(q, sk) then hit = true break end end end
                        if hit then list[#list + 1] = wp end
                    end
                end
                if #list > 0 then
                    rows[#rows + 1] = { header = slot, count = #list }
                    for i = 1, #list, cols do
                        local row = {}
                        for k = i, min(#list, i + cols - 1) do row[#row + 1] = list[k] end
                        rows[#rows + 1] = { tiles = row }
                    end
                end
            end
            local total = 0
            for _, r in ipairs(rows) do total = total + (r.header and 30 or TH + 8) end
            local off = cscroll("wmain", gx, gy, gw, gh, total, dt)
            local cy = gy - off
            for _, row in ipairs(rows) do
                local rh = row.header and 30 or TH + 8
                if cy + rh >= gy and cy <= gy + gh then
                    if row.header then
                        R.text(gx + 2, cy + 8, row.header:upper() .. "   " .. row.count, 12, T.Unselected, true)
                        R.rect(gx + 130, cy + 15, gw - 130, 1, T.Outline)
                    else
                        for c, wp in ipairs(row.tiles) do
                            local tx = gx + (c - 1) * (TW + gap)
                            local cur = (S.values.skins or {})[wp.name]
                            local sc2 = swapCount(wp.name)
                            local hot = live(tx, cy, TW, TH)
                            R.rect(tx - 1, cy - 1, TW + 2, TH + 2, (cur or sc2 > 0) and T.TabHighlight or T.Outline, 6)
                            R.rect(tx, cy, TW, TH, hot and T.GradientTop or T.GradientMid, 5)
                            local info = cur and wp.info[cur]
                            local src = (info and info.src) or wp.icon
                            local isz = TW - 28
                            local data = imageData(src)
                            if data and R.image(src, data, tx + 14, cy + 8, isz, isz) then
                                -- drawn
                            else
                                R.rect(tx + 14, cy + 8, isz, isz, T.TabButtonSelected or T.GradientTop, 4)
                                R.rect(tx + 20, cy + 14, isz - 12, 3, T.Accent, 1)
                                local initial = (wp.name:match("(%u%l*)") or wp.name:sub(1, 4)):upper()
                                R.text(tx + 14 + (isz - R.tw(initial, 13)) / 2, cy + 8 + (isz - 13) / 2, initial, 13, T.TextColor, true)
                            end
                            local nm = fit(wp.name, TW - 10, 12)
                            R.text(tx + (TW - R.tw(nm, 12)) / 2, cy + TH - 34, nm, 12, T.TextColor, true)
                            local sub = cur or (sc2 > 0 and (sc2 .. " swap" .. (sc2 == 1 and "" or "s")) or "Default")
                            sub = fit(sub, TW - 10, 11)
                            R.text(tx + (TW - R.tw(sub, 11)) / 2, cy + TH - 18, sub, 11, (cur or sc2 > 0) and T.Accent or T.Unselected, false)
                            if click(tx, cy, TW, TH) then
                                SC.weapon, SC.view = wp.name, "weapon"
                                SC.swapStep = SC.swapOwned[wp.name] and 2 or 1
                                TI.text.skinsearch = ""
                                resetScroll("skins")
                            end
                        end
                    end
                end
                cy = cy + rh
            end
            if #rows == 0 then R.text(gx + 4, gy + 6, "No weapon or skin matches.", 13, T.Unselected, false) end
            return
        end

        -- one weapon
        local weapon = wpn.name
        local cur = (S.values.skins or {})[weapon]
        hdrBack(x, y, wpn, SC.mode == "Switch" and ("Switch  -  " .. (cur or "Default")) or ("Swap  -  " .. swapCount(weapon) .. " set"))
        local hands = tostring((S.values.nohands or {})[weapon] or ""):lower() == "true"
        if btn(x + w - 350, y, 130, 30, hands and "Hands: hidden" or "Hands: shown") then
            setMapping("nohands", weapon, (not hands) and "true" or nil)
        end
        local m = seg(x + w - 214, y, 200, 30, { "Switch", "Swap" }, SC.mode == "Switch" and 1 or 2)
        if m then SC.mode = m == 1 and "Switch" or "Swap"; resetScroll("skins") end
        local gy = y + 48
        if SC.mode == "Switch" then
            R.text(x + 2, gy, "Pick what the default " .. weapon .. " looks like. Works without owning any skin.", 12, T.Unselected, false)
            gy = gy + 20
        else
            local owned = SC.swapOwned[weapon]
            local target = owned and (S.swaps[weapon] or {})[owned]
            local st = seg(x, gy, w - 14, 30, { "1  You own: " .. fit(owned or "pick", 170, 13), "2  Looks like: " .. fit(target or (owned and "pick" or "-"), 170, 13) }, SC.swapStep)
            if st == 1 or (st == 2 and owned) then SC.swapStep = st; resetScroll("skins") end
            gy = gy + 38
            local cx = x
            for o, t in pairs(S.swaps[weapon] or {}) do
                local label = fit(o .. "  >  " .. t, 220, 12)
                local cw = R.tw(label, 12) + 34
                if cx + cw > x + w - 14 then break end
                R.rect(cx, gy, cw, 22, T.TabButtonSelected, 11)
                R.text(cx + 10, gy + 4, label, 12, T.TextColor, false)
                R.text(cx + cw - 15, gy + 3, "x", 13, T.Unselected, true)
                if click(cx + cw - 22, gy, 22, 22) then setSwap(weapon, o, nil)
                elseif click(cx, gy, cw - 22, 22) then SC.swapOwned[weapon], SC.swapStep = o, 2 end
                cx = cx + cw + 6
            end
            gy = gy + 28
        end
        local q = tbox("skinsearch", x, gy, w - 14, 28, "Search skins...")
        gy = gy + 38
        local gh = y + h - gy - 22
        local gw = w - 14
        local items
        if SC.mode == "Switch" then
            items = skinItems(wpn, nil, q, true)
            local hit = tiles("skins", x, gy, gw, gh, items, function(it) if it.none then return cur == nil end return it.name == cur end, dt)
            if hit and hit.none then setMapping("skins", weapon, nil)
            elseif hit then guarded(function() setMapping("skins", weapon, hit.name) end, hit.name) end
        elseif SC.swapStep == 1 or not SC.swapOwned[weapon] then
            items = skinItems(wpn, nil, q, false, weapon)
            if #items == 0 and ownedOnly() and q == "" then R.text(x + 8, gy + 30, "You own no skins for this weapon (Skin Changer > Settings shows all).", 12, T.Unselected, false) end
            local hit = tiles("skins", x, gy, gw, gh, items, function(it) return it.name == SC.swapOwned[weapon] end, dt,
                function(it) return (S.swaps[weapon] or {})[it.name] and ">" or nil end)
            if hit then SC.swapOwned[weapon], SC.swapStep = hit.name, 2; resetScroll("skins") end
        else
            local owned = SC.swapOwned[weapon]
            local target = (S.swaps[weapon] or {})[owned]
            items = skinItems(wpn, owned, q, true)
            local hit = tiles("skins", x, gy, gw, gh, items, function(it) if it.none then return target == nil end return it.name == target end, dt)
            if hit and hit.none then setSwap(weapon, owned, nil)
            elseif hit then guarded(function() setSwap(weapon, owned, hit.name) end, hit.name) end
        end
        local count = #items - ((items[1] and items[1].none) and 1 or 0)
        R.text(x + 2, y + h - 18, count .. " skin(s) for " .. weapon, 12, T.Unselected, false)
    end

    -- cosmetics: wraps / finishers / charms --------------------------------------------------
    local COS = { { key = "wraps", label = "Wraps" }, { key = "finishers", label = "Finishers" }, { key = "charms", label = "Charms" } }
    SC.cosKind, SC.cosOwned, SC.rank = 1, {}, {}
    function SC.drawCosmetics(x, y, w, h, dt)
        footer(x, y, w, h)
        h = h - 42
        if R.clip then R.clip = { R.clip[1], R.clip[2], R.clip[3], y + h } end
        local kind = COS[SC.cosKind]
        local list = S.cat[kind.key] or {}
        local values = S.values[kind.key] or {}
        local lw = 220
        local pk = seg(x, y, lw, 30, { "Wraps", "Finishers", "Charms" }, SC.cosKind)
        if pk and pk ~= SC.cosKind then SC.cosKind = pk; resetScroll("cosown"); resetScroll("cosgrid") return end
        R.text(x + 2, y + 40, "YOU OWN", 11, T.Unselected, true)
        local q1 = tbox("cosq" .. kind.key, x, y + 58, lw, 28, "Search...")
        local names = {}
        for _, it in ipairs(list) do
            if matches(q1, it.name) and (values[it.name] ~= nil or not ownedOnly() or owns(it.name)) then names[#names + 1] = it.name end
        end
        local owned = SC.cosOwned[kind.key]
        local pick = sideList("cosown", x, y + 94, lw - 12, h - 94, names, owned, function(n) return values[n] ~= nil end, dt)
        if pick then SC.cosOwned[kind.key] = pick; resetScroll("cosgrid") end
        owned = SC.cosOwned[kind.key]
        local rx, rw = x + lw + 14, w - lw - 14
        R.rect(rx - 8, y, 1, h, T.Outline)
        if not owned then
            R.text(rx, y + 8, "Pick one you own on the left, then what it should look like.", 14, T.TextColor, false)
            R.text(rx, y + 30, "Saved as Owned=Target: the game shows the target wherever the owned one would be.", 12, T.Unselected, false)
            return
        end
        local target = values[owned]
        local season = target and target:match("^(Season %d+)%s")
        R.text(rx, y, owned, 16, T.TextColor, true)
        R.text(rx, y + 21, "looks like  " .. (target or "itself"), 12, T.Unselected, false)
        local gy = y + 46
        if kind.key == "charms" and season then
            local current = target:match("^Season %d+%s+(.+)$") or RANKS[1]
            local ri = 1
            for i, r in ipairs(RANKS) do if r == current then ri = i end end
            R.text(rx, gy + 6, "Rank", 13, T.Unselected, false)
            if btn(rx + 50, gy, 30, 26, "<") then ri = max(1, ri - 1); setMapping("charms", owned, season .. " " .. RANKS[ri]) end
            R.text(rx + 130 - R.tw(RANKS[ri], 13) / 2, gy + 6, RANKS[ri], 13, T.Accent, true)
            if btn(rx + 190, gy, 30, 26, ">") then ri = min(#RANKS, ri + 1); setMapping("charms", owned, season .. " " .. RANKS[ri]) end
            gy = gy + 34
        end
        local q2 = tbox("costq" .. kind.key, rx, gy, rw - 14, 28, "Search looks like...")
        gy = gy + 38
        local items = { { name = "None", none = true } }
        for _, it in ipairs(list) do if it.name ~= owned and matches(q2, it.name) then items[#items + 1] = it end end
        local hit = tiles("cosgrid", rx, gy, rw - 14, y + h - gy - 4, items, function(it)
            if it.none then return target == nil end
            return it.name == target or (season ~= nil and it.name == season)
        end, dt)
        if hit then
            if hit.none then setMapping(kind.key, owned, nil)
            elseif kind.key == "charms" and hit.name:match("^Season %d+$") then
                guarded(function() setMapping("charms", owned, hit.name .. " " .. (SC.rank[owned] or RANKS[1])) end, hit.name)
            else
                guarded(function() setMapping(kind.key, owned, hit.name) end, hit.name)
            end
        end
    end

    -- sky: skybox grid with pictures (writes [Skybox] Preset) --------------------------------
    function SC.drawSkies(x, y, w, h, dt)
        footer(x, y, w, h)
        h = h - 42
        if R.clip then R.clip = { R.clip[1], R.clip[2], R.clip[3], y + h } end
        local now = ((S.values.skybox or {}).Preset or ""):lower()
        R.text(x + 2, y, "Skybox", 16, T.TextColor, true)
        R.text(x + 2, y + 21, now ~= "" and ("Now: " .. now .. "  (Save & Apply, shows on next map load)") or "Now: the game's own sky", 12, T.Unselected, false)
        local q = tbox("skyq", x + w - 262, y, 248, 30, "Search skies...")
        local items = {}
        if q == "" then items[1] = { name = "Off", none = true } end
        for _, g in ipairs(X.SKY_GROUPS) do
            for _, s in ipairs(g.skies) do
                if matches(q, s) then
                    local face = S.cat.skyFace[s]
                    local it = { name = s, src = face and ("assets/images/skies/" .. face .. ".png") or nil }
                    if s == "gray" then it.color = pack(128, 128, 128) elseif s == "black" then it.color = pack(8, 8, 10) elseif s == "classic" then it.color = pack(116, 160, 214) end
                    items[#items + 1] = it
                end
            end
        end
        local hit = tiles("skygrid", x, y + 46, w - 14, h - 46, items, function(it) if it.none then return now == "" end return it.name == now end, dt)
        if hit then
            for _, key in ipairs({ "All", "BK", "DN", "FT", "LF", "RT", "UP" }) do setMapping("skybox", key, nil) end
            setMapping("skybox", "Preset", (not hit.none) and hit.name or nil)
        end
    end
    function SC.drawFooterOnly(x, y, w, h) footer(x, y, w, h) end

    -- links: config <-> UI items (tracers, hands, sounds) ----------------------------------
    function X.link(proxy, key, get, set)
        X.links[#X.links + 1] = { t = proxy, k = key, get = get, set = set, last = proxy[key] }
    end
    function X.linkTick()
        if not S.readable then return end
        for _, l in ipairs(X.links) do
            local cur = l.get()
            if l.t[l.k] ~= l.last then
                l.last = l.t[l.k]
                l.set(l.t[l.k])
            elseif cur ~= nil and cur ~= l.t[l.k] then
                l.t[l.k] = cur
                l.last = cur
            end
        end
    end

    ----------------------------------------------------------------------
    -- GUN / MELEE MODS (Matcha's getgc / applygc: weapon stats live in the game's Lua tables)
    ----------------------------------------------------------------------
    local GUN_NAMES = { "ShootRecoil", "ShootSpread", "ShootAccuracy", "ShootCooldown", "ProjectileSpeed" }
    local MELEE_NAMES = { "AttackCooldown", "SwingCooldown", "MeleeCooldown", "RecoveryTime" }
    Gun.status, Gun.cache, Gun.cacheT, Gun.orig, Gun.applied, Gun.lastApply, Gun.found = "idle", nil, -100, {}, 0, 0, 0
    Gun.wasOn = false
    Gun.scanning = false

    local function hasGC() return type(getgc) == "function" and type(applygc) == "function" end

    function Gun.names()
        local names = {}
        for _, n in ipairs(GUN_NAMES) do names[#names + 1] = n end
        for _, n in ipairs(MELEE_NAMES) do names[#names + 1] = n end
        if Cfg.Melee.generic then names[#names + 1] = "Cooldown"; names[#names + 1] = "ResetTime" end
        return names
    end

    function Gun.applyNow()
        if not (Gun.cache and #Gun.cache > 0) then return end
        local vals = Gun.values()
        if next(vals) then
            local ok, n = pcall(applygc, Gun.cache, vals)
            if ok then
                Gun.applied = tonumber(n) or 0
                Gun.status = string.format("active: %d values set (%d found)", Gun.applied, Gun.found)
            else
                Gun.status = "applygc failed: " .. tostring(n):sub(1, 60)
            end
        end
    end

    function Gun.scan(force)
        if Gun.scanning then return end
        if not hasGC() then Gun.status = "getgc/applygc not available" return end
        if Gun.cache and not force then return end
        Gun.scanning = true
        Gun.status = "scanning in background..."
        task.spawn(function()
            local ok, res = pcall(getgc, Gun.names())
            Gun.scanning = false
            if not ok or type(res) ~= "table" then
                Gun.status = "getgc failed: " .. tostring(res):sub(1, 60)
                return
            end
            Gun.cache, Gun.cacheT, Gun.found = res, tick(), #res
            for _, e in ipairs(res) do
                if type(e) == "table" and e.type == "number" and e.addr and Gun.orig[e.addr] == nil then
                    Gun.orig[e.addr] = { key = e.key, v = e.value }
                end
            end
            Gun.status = string.format("scanned: %d found", Gun.found)
            Gun.applyNow()
        end)
    end
    Gun.refresh = function() Gun.scan(true) return true end

    function Gun.values()
        local g, m, v = Cfg.Gun, Cfg.Melee, {}
        if g.enabled then
            if g.recOn then v.ShootRecoil = g.recoil end
            if g.sprOn then v.ShootSpread = g.spread end
            if g.accOn then v.ShootAccuracy = g.accuracy end
            if g.cdOn then v.ShootCooldown = g.cooldown end
            if g.spdOn then v.ProjectileSpeed = g.projSpeed end
        end
        if m.enabled then
            for _, n in ipairs(MELEE_NAMES) do v[n] = m.cd end
            if m.generic then v.Cooldown = m.cd; v.ResetTime = m.cd end
        end
        return v
    end

    function Gun.restore()
        local n = 0
        for addr, o in pairs(Gun.orig) do
            if type(o.v) == "number" and pcall(memory_write, "double", addr, o.v) then n = n + 1 end
        end
        Gun.orig, Gun.cache, Gun.cacheT = {}, nil, -100
        Gun.status = n > 0 and ("restored " .. n .. " values to default") or "nothing to restore"
    end

    Gun.lastShoot = 0
    function Gun.fullAutoTick()
        local g = Cfg.Gun
        if not (g and g.fullAuto) then return end
        if UI.open or (type(isrbxactive) == "function" and not isrbxactive()) then return end
        if ismouse1pressed and ismouse1pressed() then
            local now = tick()
            local delay = math.max(0.015, (g.autoDelay or 25) / 1000)
            if now - Gun.lastShoot >= delay then
                Gun.lastShoot = now
                if mouse1click then mouse1click() end
            end
        end
    end

    function Gun.tick()
        Gun.fullAutoTick()
        local on = Cfg.Gun.enabled or Cfg.Melee.enabled
        if not on then
            if Gun.wasOn then Gun.restore() end
            Gun.wasOn = false
            return
        end
        Gun.wasOn = true
        if not Gun.cache then
            if not Gun.scanning then Gun.scan(false) end
            return
        end
        local now = tick()
        if now - Gun.lastApply < 0.3 then return end
        Gun.lastApply = now
        Gun.applyNow()
    end

    ----------------------------------------------------------------------
    -- SILENT AIM: the camera is pointed at the target for the click frame only, then put back.
    -- The cursor is never moved. (Needs the camera rotation memory to be calibrated.)
    ----------------------------------------------------------------------
    SA.status, SA.phase, SA.last, SA.saved, SA.shots = "idle", 0, 0, nil, 0
    local function camWrite(r)
        local cam = camera()
        local addr = cam and try(function() return cam.Address end)
        if not (hasMem and validPtr(addr)) then return false end
        for i = 1, 9 do memory_write("float", addr + OFF.CameraRotation + (i - 1) * 4, r[i]) end
        return true
    end
    function SA.lookAt(dir)
        if not Cam.choice then return false end
        local cam = camera()
        local addr = cam and try(function() return cam.Address end)
        if not validPtr(addr) then return false end
        -- right = dir x up(0,1,0)
        local rx, ry, rz = -dir.Z, 0, dir.X
        local rm = sqrt(rx * rx + ry * ry + rz * rz)
        if rm < 0.001 then rx, ry, rz, rm = 1, 0, 0, 1 end
        rx, ry, rz = rx / rm, ry / rm, rz / rm
        -- up' = right x dir
        local ux, uy, uz = ry * dir.Z - rz * dir.Y, rz * dir.X - rx * dir.Z, rx * dir.Y - ry * dir.X
        local bx, by, bz = -dir.X, -dir.Y, -dir.Z
        local r
        if Cam.choice == "A" then r = { rx, ux, bx, ry, uy, by, rz, uz, bz }
        else r = { rx, ry, rz, ux, uy, uz, bx, by, bz } end
        if not SA.saved then SA.saved = readRot(addr) end
        return camWrite(r)
    end
    function SA.restore()
        if SA.saved then camWrite(SA.saved); SA.saved = nil end
        SA.phase = 0
    end
    function SA.pick(c)
        local myRoot = myParts()
        if not myRoot then return nil end
        local cam = camera()
        local camPos = cam and try(function() return cam.Position end)
        if not camPos then return nil end
        local vw, vh = viewport()
        local best, bd, bpos = nil, c.fov, nil
        for _, e in ipairs(Targets.list) do
            if e.alive and (not c.teamCheck or e.enemy) then
                local ok, pos = pcall(Targets.pos, e, c.part == "Torso" and "Torso" or "Head")
                if ok and (pos - myRoot.Position).Magnitude <= c.maxDist then
                    if c.predict then
                        local v = try(function() return e.root.AssemblyLinearVelocity end)
                        if v then pos = pos + v * (c.predictMs / 1000) end
                    end
                    local sx, sy = w2s(pos)
                    if sx then
                        local d = sqrt((sx - vw / 2) ^ 2 + (sy - vh / 2) ^ 2)
                        if d < bd then best, bd, bpos = e, d, pos end
                    end
                end
            end
        end
        return best, bpos, camPos
    end
    function SA.tick()
        local c = Cfg.Silent
        if SA.phase > 0 then
            -- phase 1: camera was moved last frame -> click now; phase 2: put the camera back
            if SA.phase == 1 then
                if not (UI.open or not isrbxactive()) then mouse1click() SA.shots = SA.shots + 1 end
                SA.phase = 2
                return
            end
            SA.restore()
            SA.last = tick()
            return
        end
        if not featureOn(c) then SA.status = "idle" return end
        if UI.open or not isrbxactive() then return end
        if not (c.autoFire or ismouse1pressed()) then SA.status = "waiting for mouse1" return end
        if tick() - SA.last < c.delay / 1000 then return end
        local e, pos, camPos = SA.pick(c)
        if not e then SA.status = "no target in FOV" return end
        Cam.look()
        if not Cam.choice then SA.status = "needs camera memory (see diagnostics)" return end
        local dir = pos - camPos
        if dir.Magnitude < 0.5 then return end
        if SA.lookAt(dir.Unit) then
            SA.phase = 1
            SA.status = "shooting " .. e.name
        else
            SA.status = "camera write failed"
        end
    end
    function SA.draw()
        local c = Cfg.Silent
        if c.enabled and c.showFov then
            local vw, vh = viewport()
            R.circle(vw / 2, vh / 2, c.fov, c.fovColor, false, 1, 64)
        end
    end

    ----------------------------------------------------------------------
    -- WORLD: lighting writes (if Matcha allows them) + Drawing-based weather and screen effects
    ----------------------------------------------------------------------
    Lit.svc, Lit.orig, Lit.last, Lit.errors, Lit.active, Lit.status = nil, {}, {}, {}, false, "idle"
    Lit.skyOrig, Lit.skyLast, Lit.skyNode = {}, nil, nil
    local function c3(p) local r, g, b = rgb3(p) return Color3.fromRGB(r, g, b) end
    function Lit.get()
        if not Lit.svc then Lit.svc = try(function() return game:GetService("Lighting") end) end
        return Lit.svc
    end
    function Lit.set(prop, val)
        local svc = Lit.get()
        if not svc or Lit.errors[prop] then return end
        if Lit.orig[prop] == nil then
            local ok, cur = pcall(function() return svc[prop] end)
            if ok and cur ~= nil then Lit.orig[prop] = cur else Lit.errors[prop] = "unreadable" return end
        end
        local key = type(val) == "userdata" and tostring(val) or val
        if Lit.last[prop] == key then return end
        local ok, err = pcall(function() svc[prop] = val end)
        if ok then Lit.last[prop] = key else Lit.errors[prop] = tostring(err):sub(1, 50) end
    end
    function Lit.restoreAll()
        local svc = Lit.get()
        if svc then
            for prop, v in pairs(Lit.orig) do pcall(function() svc[prop] = v end) end
        end
        Lit.last = {}
        local sk = Lit.skyNode
        if sk then for prop, v in pairs(Lit.skyOrig) do pcall(function() sk[prop] = v end) end end
        Lit.skyOrig, Lit.skyLast = {}, nil
    end
    local SKY_PROPS = { ft = "SkyboxFt", bk = "SkyboxBk", dn = "SkyboxDn", lf = "SkyboxLf", rt = "SkyboxRt", up = "SkyboxUp" }
    function Lit.tick()
        local w = Cfg.World
        local L, S2 = w.light, w.sky
        if not (L.enabled or S2.enabled) then
            if Lit.active then Lit.restoreAll(); Lit.active = false; Lit.status = "restored" end
            return
        end
        Lit.active = true
        if L.enabled then
            if L.timeOn then Lit.set("ClockTime", L.time) end
            if L.brightOn then Lit.set("Brightness", L.bright) end
            if L.expOn then Lit.set("ExposureCompensation", L.exposure) end
            if L.ambOn then Lit.set("Ambient", c3(L.amb)) end
            if L.outOn then Lit.set("OutdoorAmbient", c3(L.out)) end
            if L.shiftOn then Lit.set("ColorShift_Top", c3(L.shift)) end
            if L.fogOn then
                Lit.set("FogEnd", L.fogEnd)
                Lit.set("FogStart", L.fogStart)
                Lit.set("FogColor", c3(L.fog))
            end
            local bad = 0
            for _ in pairs(Lit.errors) do bad = bad + 1 end
            Lit.status = bad > 0 and (bad .. " lighting props rejected") or "writing"
        end
        if S2.enabled then
            local svc = Lit.get()
            local sk = svc and try(function() return svc:FindFirstChildOfClass("Sky") end)
            Lit.skyNode = sk
            local faces = S.cat.skyFull[S2.pick]
            if not faces then
                local f = S.cat.skyFace[S2.pick]
                if f then faces = { ft = f, bk = f, dn = f, lf = f, rt = f, up = f } end
            end
            if not sk then
                Lit.skyStatus = "no Sky object in Lighting"
            elseif not faces then
                Lit.skyStatus = S.cat.loaded and "no pictures known for that sky" or "sky lists not loaded yet"
            elseif Lit.skyLast ~= S2.pick then
                local okAll = true
                for k, prop in pairs(SKY_PROPS) do
                    local id = faces[k] or faces.ft
                    if id then
                        if Lit.skyOrig[prop] == nil then
                            local okR, cur = pcall(function() return sk[prop] end)
                            if okR then Lit.skyOrig[prop] = cur end
                        end
                        if not pcall(function() sk[prop] = "rbxassetid://" .. tostring(id) end) then okAll = false end
                    end
                end
                Lit.skyLast = S2.pick
                Lit.skyStatus = okAll and ("sky set: " .. S2.pick) or "sky writes rejected by Matcha"
            end
        else
            Lit.skyStatus = nil
        end
    end

    -- weather particles + colour overlays ------------------------------------------
    local flakes, drops = {}, {}
    local flash, nextFlash, hueT = 0, 0, 0
    function FX.draw(dt)
        local w = Cfg.World
        local vw, vh = viewport()
        local d = clamp(dt, 0.001, 0.05)
        -- overlays first, so the menu draws on top of them
        local t = w.tint
        if t.enabled then
            local col = t.color
            if t.rainbow then hueT = (hueT + d * t.rspeed) % 1; col = hsv2c(hueT, 0.7, 1) end
            R.rect(0, 0, vw, vh, col, 0, t.alpha)
        end
        if w.dim.enabled then R.rect(0, 0, vw, vh, 0, 0, w.dim.alpha) end
        if w.vignette.enabled then
            local al = w.vignette.alpha * 0.14
            for i = 1, 6 do
                local band = 30 * i
                R.rect(0, 0, band, vh, 0, 0, al)
                R.rect(vw - band, 0, band, vh, 0, 0, al)
                R.rect(0, 0, vw, band * 0.6, 0, 0, al)
                R.rect(0, vh - band * 0.6, vw, band * 0.6, 0, 0, al)
            end
        end
        local s = w.snow
        if s.enabled then
            local n = floor(s.amount)
            while #flakes < n do
                flakes[#flakes + 1] = { x = random() * vw, y = random() * vh, z = 0.4 + random() * 0.6, ph = random() * 6.28 }
            end
            while #flakes > n do flakes[#flakes] = nil end
            for _, f in ipairs(flakes) do
                f.y = f.y + (40 + 90 * f.z) * s.speed * d
                f.ph = f.ph + d * 1.5
                f.x = f.x + (sin(f.ph) * 18 + s.wind * 120) * f.z * d
                if f.y > vh + 6 then f.y = -6; f.x = random() * vw end
                if f.x > vw + 6 then f.x = -6 elseif f.x < -6 then f.x = vw + 6 end
                R.circle(f.x, f.y, max(1, s.size * f.z), s.color, true, 1, 8)
            end
        else
            flakes = {}
        end
        local r = w.rain
        if r.enabled then
            local n = floor(r.amount)
            while #drops < n do
                drops[#drops + 1] = { x = random() * (vw + 200) - 100, y = random() * vh, z = 0.6 + random() * 0.4 }
            end
            while #drops > n do drops[#drops] = nil end
            local sl = r.wind * 0.6
            for _, p in ipairs(drops) do
                p.y = p.y + 900 * p.z * r.speed * d
                p.x = p.x + 900 * p.z * r.speed * d * sl
                if p.y > vh + 20 then p.y = -20; p.x = random() * (vw + 200) - 100 end
                R.line(p.x, p.y, p.x + r.len * sl * p.z, p.y + r.len * p.z, r.color, 1)
            end
            if r.thunder then
                nextFlash = nextFlash - d
                if nextFlash <= 0 then flash = 1; nextFlash = 4 + random() * 9 end
            end
        else
            drops = {}
        end
        if flash > 0 then
            R.rect(0, 0, vw, vh, pack(255, 255, 255), 0, flash * 0.55)
            flash = max(0, flash - d * 2.2)
        end
    end

    return X
end)()
K.ext = Ext
local ExtSC, ExtGun, ExtSA, ExtFX, ExtLit = Ext.SC, Ext.Gun, Ext.SA, Ext.FX, Ext.Lit

Store.onLoad = function()
    if (Cfg.Gun and Cfg.Gun.enabled) or (Cfg.Melee and Cfg.Melee.enabled) then
        ExtGun.scan(true)
        ExtGun.applyNow()
    else
        if ExtGun and ExtGun.wasOn then
            ExtGun.restore()
        end
    end
end

pcall(function()
    if ExtSC.autoLoad then
        ExtSC.loadConfig()
    end
    ExtSC.loadCatalog()
    if ExtSC.autoApply then
        task.delay(1.5, function()
            pcall(ExtSC.apply)
        end)
    end
end)
pcall(function()
    LocalPlayer.CharacterAdded:Connect(function()
        if Cfg.Gun.enabled or Cfg.Melee.enabled then
            ExtGun.scan(true)
        end
    end)
end)
if Cfg.Gun.enabled or Cfg.Melee.enabled then
    pcall(Store.onLoad)
end

-- pages -----------------------------------------------------------------------
local function espSection(title, sc, side)
    return { title = title, side = side, items = {
        Toggle("Enable " .. title .. " ESP", sc, "enabled"),
        Toggle("Name", sc.name, "on", { color = { sc.name, "color" } }),
        Toggle("Box", sc.box, "on", { color = { sc.box, "color" } }),
        Drop("Box Style", sc.box, "style", { "Full", "Corner" }),
        Toggle("Health Bar", sc.health, "on"),
        Toggle("Health Number", sc.healthNum, "on", { color = { sc.healthNum, "color" } }),
        Toggle("Distance", sc.distance, "on", { color = { sc.distance, "color" } }),
        Toggle("Tracer", sc.tracer, "on", { color = { sc.tracer, "color" } }),
        Drop("Tracer From", sc.tracer, "origin", { "Bottom", "Center", "Top", "Mouse" }),
        Toggle("Head Marker", sc.head, "on", { color = { sc.head, "color" } }),
        Toggle("Skeleton", sc.skeleton, "on", { color = { sc.skeleton, "color" } }),
    } }
end

local Pages = (function()
local RB, EV = Cfg.Ragebot, Cfg.Ragebot.evasion
-- ---- data + links for the Skin Changer extras and the World / Gun pages ----
local SKY_GROUP_NAMES, SKY_OPTS, skyShown = {}, {}, nil
for _, g in ipairs(Ext.SKY_GROUPS) do SKY_GROUP_NAMES[#SKY_GROUP_NAMES + 1] = g.name end
local function refreshSky()
    local sk = Cfg.World.sky
    if skyShown == sk.group then return true end
    skyShown = sk.group
    for i = #SKY_OPTS, 1, -1 do SKY_OPTS[i] = nil end
    local found = false
    for _, g in ipairs(Ext.SKY_GROUPS) do
        if g.name == sk.group then
            for _, s in ipairs(g.skies) do SKY_OPTS[#SKY_OPTS + 1] = s; if s == sk.pick then found = true end end
        end
    end
    if not found and SKY_OPTS[1] then sk.pick = SKY_OPTS[1] end
    return true
end
refreshSky()

local TRACER_NAMES, TRACER_HEX = { "Game's own", "Rainbow", "Red", "Orange", "Gold", "Yellow", "Lime", "Green", "Mint", "Cyan", "Blue", "Purple", "Pink", "White" },
    { Rainbow = "rainbow", Red = "ff2d2d", Orange = "ff7a00", Gold = "ffc400", Yellow = "ffee00", Lime = "a6ff00", Green = "2dff5a",
        Mint = "00ffa6", Cyan = "00e5ff", Blue = "2d6bff", Purple = "8a2dff", Pink = "ff4fd8", White = "ffffff" }
local XT = { color = "Game's own", speed = 100, energy = false, hands = false }
local function cfgv(section, key) return (ExtSC.S.values[section] or {})[key] end
Ext.link(XT, "color", function()
    local v = cfgv("tracers", "Color")
    if not v then return "Game's own" end
    v = tostring(v):lower()
    for n, hex in pairs(TRACER_HEX) do if hex == v then return n end end
    return nil
end, function(name) ExtSC.setMapping("tracers", "Color", TRACER_HEX[name]) end)
Ext.link(XT, "speed", function() return tonumber(cfgv("tracers", "Speed")) or 100 end,
    function(v) ExtSC.setMapping("tracers", "Speed", v ~= 100 and tostring(floor(v)) or nil) end)
Ext.link(XT, "energy", function() return tostring(cfgv("tracers", "EnergyPistolsTracers") or ""):lower() == "true" end,
    function(v) ExtSC.setMapping("tracers", "EnergyPistolsTracers", v and "true" or nil) end)
Ext.link(XT, "hands", function() return tostring(cfgv("nohands", "All") or ""):lower() == "true" end,
    function(v) ExtSC.setMapping("nohands", "All", v and "true" or nil) end)

local SND = { group = "Rivals", Hit = "Game default", Critical = "Game default", Kill = "Game default" }
local SND_GROUPS, SND_OPTS, sndShown = {}, {}, nil
for _, g in ipairs(Ext.SOUNDS) do SND_GROUPS[#SND_GROUPS + 1] = g.name end
local function refreshSounds()
    if sndShown == SND.group then return true end
    sndShown = SND.group
    for i = #SND_OPTS, 1, -1 do SND_OPTS[i] = nil end
    SND_OPTS[1], SND_OPTS[2] = "Game default", "Mute"
    for _, g in ipairs(Ext.SOUNDS) do
        if g.name == SND.group then for _, s in ipairs(g.sounds) do SND_OPTS[#SND_OPTS + 1] = s[1] end end
    end
    return true
end
refreshSounds()
local function soundId(name)
    if name == "Game default" then return nil end
    if name == "Mute" then return "none" end
    for _, g in ipairs(Ext.SOUNDS) do for _, s in ipairs(g.sounds) do if s[1] == name then return s[2] end end end
    return nil
end
for _, slot in ipairs({ "Hit", "Critical", "Kill" }) do
    Ext.link(SND, slot, function()
        local v = cfgv("sounds", slot)
        if not v then return "Game default" end
        v = tostring(v):lower()
        if v == "none" then return "Mute" end
        for _, g in ipairs(Ext.SOUNDS) do for _, s in ipairs(g.sounds) do if s[2] == v then return s[1] end end end
        return nil
    end, function(name) ExtSC.setMapping("sounds", slot, soundId(name)) end)
end

local P = {
    { name = "Combat", glyph = "crosshair", subs = {
        { name = "Aimbot", desc = "Camera-based aim assistance and target locking.", sections = {
            { title = "Aimbot", side = "left", items = {
                Toggle("Enabled", Cfg.Aimbot, "enabled", { bind = Cfg.Aimbot.bind }),
                Toggle("Team Check", Cfg.Aimbot, "teamCheck"),
                Drop("Hit Part", Cfg.Aimbot, "part", { "Head", "Torso" }),
                Slider("Smoothness", Cfg.Aimbot, "smooth", 1, 50, 1),
                Slider("Distance", Cfg.Aimbot, "maxDist", 50, 3000, 10),
            } },
            { title = "FOV", side = "right", items = {
                Toggle("Show FOV", Cfg.Aimbot, "showFov", { color = { Cfg.Aimbot, "fovColor" } }),
                Slider("Size", Cfg.Aimbot, "fov", 20, 600, 1),
                Drop("Aim Origin", Cfg.Aimbot, "origin", { "Center", "Cursor" }),
            } },
            { title = "Prediction", side = "right", items = {
                Toggle("Velocity Prediction", Cfg.Aimbot, "predict"),
                Slider("Lead Time", Cfg.Aimbot, "predictMs", 0, 300, 5, "ms"),
            } },
        } },
        { name = "Ragebot", desc = "Aggressive targeting, weapon priority, and evasive movement.", sections = {
            { title = "Activation", side = "left", items = {
                Toggle("Enable Ragebot", RB, "enabled", { bind = RB.bind }),
                Toggle("Team Check", RB, "teamCheck"),
                Drop("Target Priority", RB, "priority", { "Closest", "Lowest Health", "Closest To Crosshair" }),
                Slider("Distance", RB, "maxDist", 50, 5000, 10),
                Slider("Shoot Frames", RB, "shootFrames", 1, 5, 1),
                Toggle("Auto Fire", RB, "autoFire"),
            } },
            { title = "Weapon Strategy", side = "left", items = {
                Drop("Auto Equip", RB, "equip", { "Off", "Primary", "Secondary", "Melee" }),
                Stat("Teleport Write", function()
                    local good = Rage.tp == "OK"
                    return Rage.tp, (good and T.Accent) or ((Rage.tp == "untested") and T.Unselected or pack(220, 90, 90))
                end),
                Stat("Status", function() return Rage.status, T.TextColor end),
            } },
            { title = "Evasion", side = "right", items = {
                Drop("Evasion Mode", EV, "mode", { "Off", "Random", "Translocate" }),
                Slider("Evade Frames", EV, "evadeFrames", 1, 5, 1, "", function() return EV.mode ~= "Off" end),
                Slider("Aim Distance", RB.glue, "dist", 2, 40, 0.5),
                Divider("Random", function() return EV.mode == "Random" end),
                Drop("Anchor", EV, "anchor", { "Target", "Character", "Origin" }, function() return EV.mode == "Random" end),
                Slider("Base Radius", EV, "radius", 5, 500, 1, "", function() return EV.mode == "Random" end),
                Slider("Random Factor", EV, "factor", 0, 1, 0.1, "", function() return EV.mode == "Random" end),
                Slider("Height Range", EV, "yRange", 0, 100, 1, "", function() return EV.mode == "Random" end),
                Stat("Translocate", function() return Translocate.status, T.TextColor end),
            } },
        } },
        { name = "Fire Assist", desc = "Automatic firing when your crosshair is on a target.", sections = {
            { title = "Triggerbot", side = "left", items = {
                Toggle("Enabled", Cfg.Trigger, "enabled", { bind = Cfg.Trigger.bind }),
                Toggle("Team Check", Cfg.Trigger, "teamCheck"),
                Slider("Radius", Cfg.Trigger, "radius", 2, 80, 1, "px"),
                Slider("Shot Delay", Cfg.Trigger, "delay", 0, 250, 1, "ms"),
                Slider("Cooldown", Cfg.Trigger, "cooldown", 0, 1000, 5, "ms"),
            } },
        } },
        { name = "Silent Aim", desc = "Hits without moving your cursor: the camera snaps for the shot frame only, then returns.", sections = {
            { title = "Silent Aim", side = "left", items = {
                Toggle("Enabled", Cfg.Silent, "enabled", { bind = Cfg.Silent.bind }),
                Toggle("Team Check", Cfg.Silent, "teamCheck"),
                Drop("Hit Part", Cfg.Silent, "part", { "Head", "Torso" }),
                Slider("Distance", Cfg.Silent, "maxDist", 50, 3000, 10),
                Toggle("Auto Fire", Cfg.Silent, "autoFire"),
                Slider("Shot Delay", Cfg.Silent, "delay", 20, 500, 5, "ms"),
                Stat("Status", function() return ExtSA.status, T.TextColor end),
                Stat("Shots", function() return tostring(ExtSA.shots), T.TextColor end),
            } },
            { title = "FOV", side = "right", items = {
                Toggle("Show FOV", Cfg.Silent, "showFov", { color = { Cfg.Silent, "fovColor" } }),
                Slider("Size", Cfg.Silent, "fov", 20, 600, 1),
            } },
            { title = "Prediction", side = "right", items = {
                Toggle("Velocity Prediction", Cfg.Silent, "predict"),
                Slider("Lead Time", Cfg.Silent, "predictMs", 0, 300, 5, "ms"),
            } },
        } },
    } },
    { name = "Player", glyph = "player", subs = {
        { name = "Movement", desc = "Fly, speed, and character movement.", sections = {
            { title = "Fly", side = "left", items = {
                Toggle("Enabled", Cfg.Movement.fly, "enabled", { bind = Cfg.Movement.fly.bind }),
                Drop("Mode", Cfg.Movement.fly, "mode", { "Velocity", "Position" }),
                Slider("Speed", Cfg.Movement.fly, "speed", 5, 500, 1),
                Stat("Camera Look", function() return Cam.mode, T.TextColor end),
            } },
            { title = "Speed", side = "right", items = {
                Toggle("Enabled", Cfg.Movement.speed, "enabled", { bind = Cfg.Movement.speed.bind }),
                Slider("Speed", Cfg.Movement.speed, "value", 16, 300, 1),
            } },
        } },
        { name = "Character", desc = "Collision and jump behaviour.", sections = {
            { title = "Noclip", side = "left", items = {
                Toggle("Enabled", Cfg.Movement.noclip, "enabled", { bind = Cfg.Movement.noclip.bind }),
            } },
            { title = "Infinite Jump", side = "right", items = {
                Toggle("Enabled", Cfg.Movement.jump, "enabled", { bind = Cfg.Movement.jump.bind }),
                Slider("Jump Power", Cfg.Movement.jump, "power", 10, 300, 1),
            } },
        } },
    } },
    { name = "Visuals", glyph = "eye", subs = {
        { name = "Player ESP", desc = "Boxes, names, health, and tracers for every player.", sections = {
            { title = "Player ESP", side = "left", items = {
                Toggle("Enable ESP", Cfg.Esp, "enabled", { bind = Cfg.Esp.bind }),
                Slider("Distance", Cfg.Esp, "maxDist", 50, 5000, 10),
                Slider("Font Size", Cfg.Esp, "textSize", 8, 24, 1),
            } },
            espSection("Enemies", Cfg.Esp.Enemy, "left"),
            espSection("Teammates", Cfg.Esp.Team, "right"),
        } },
        { name = "Crosshair", desc = "Custom crosshair drawn at the screen centre.", sections = {
            { title = "Crosshair", side = "left", items = {
                Toggle("Enabled", Cfg.Crosshair, "enabled", { color = { Cfg.Crosshair, "color" } }),
                Slider("Size", Cfg.Crosshair, "size", 2, 40, 1),
                Slider("Gap", Cfg.Crosshair, "gap", 0, 30, 1),
                Slider("Thickness", Cfg.Crosshair, "thick", 1, 6, 1),
                Toggle("Center Dot", Cfg.Crosshair, "dot"),
            } },
        } },
    } },
    { name = "World", glyph = "globe", subs = {
        { name = "Atmosphere", desc = "Lighting overrides written straight to the game (restored when turned off).", sections = {
            { title = "Lighting", side = "left", items = {
                Toggle("Enable Overrides", Cfg.World.light, "enabled"),
                Toggle("Time Of Day", Cfg.World.light, "timeOn"),
                Slider("Clock Time", Cfg.World.light, "time", 0, 24, 0.1),
                Toggle("Brightness", Cfg.World.light, "brightOn"),
                Slider("Brightness Value", Cfg.World.light, "bright", 0, 10, 0.1),
                Toggle("Exposure", Cfg.World.light, "expOn"),
                Slider("Exposure Value", Cfg.World.light, "exposure", -3, 3, 0.1),
                Stat("Status", function() return ExtLit.status, T.TextColor end),
            } },
            { title = "Colors", side = "right", items = {
                Toggle("Ambient", Cfg.World.light, "ambOn", { color = { Cfg.World.light, "amb" } }),
                Toggle("Outdoor Ambient", Cfg.World.light, "outOn", { color = { Cfg.World.light, "out" } }),
                Toggle("Color Shift", Cfg.World.light, "shiftOn", { color = { Cfg.World.light, "shift" } }),
            } },
            { title = "Fog", side = "right", items = {
                Toggle("Fog", Cfg.World.light, "fogOn", { color = { Cfg.World.light, "fog" } }),
                Slider("Fog Start", Cfg.World.light, "fogStart", 0, 5000, 10),
                Slider("Fog End", Cfg.World.light, "fogEnd", 50, 20000, 50),
            } },
        } },
        { name = "Sky", desc = "Custom skyboxes: live swap, or write it to the Rivals config for the changer.", sections = {
            { title = "Skybox", side = "left", items = {
                Toggle("Live Sky Swap", Cfg.World.sky, "enabled"),
                Drop("Category", Cfg.World.sky, "group", SKY_GROUP_NAMES, refreshSky),
                Drop("Sky", Cfg.World.sky, "pick", SKY_OPTS, refreshSky),
                Stat("Live Status", function() return ExtLit.skyStatus or "off", T.TextColor end),
            } },
            { title = "Changer", side = "right", items = {
                Button("Use This Sky In Config", function() ExtSC.setMapping("skybox", "Preset", Cfg.World.sky.pick) end),
                Button("Save & Apply Config", function() ExtSC.job("Applying...", ExtSC.apply) end),
                Stat("Status", function() return ExtSC.S.status, T.TextColor end),
            } },
        } },
        { name = "Weather", desc = "Snow, rain and thunder drawn over your screen.", sections = {
            { title = "Snow", side = "left", items = {
                Toggle("Enabled", Cfg.World.snow, "enabled", { color = { Cfg.World.snow, "color" } }),
                Slider("Amount", Cfg.World.snow, "amount", 10, 500, 5),
                Slider("Speed", Cfg.World.snow, "speed", 0.2, 4, 0.1),
                Slider("Flake Size", Cfg.World.snow, "size", 1, 8, 0.5),
                Slider("Wind", Cfg.World.snow, "wind", -1, 1, 0.1),
            } },
            { title = "Rain", side = "right", items = {
                Toggle("Enabled", Cfg.World.rain, "enabled", { color = { Cfg.World.rain, "color" } }),
                Slider("Amount", Cfg.World.rain, "amount", 20, 500, 5),
                Slider("Speed", Cfg.World.rain, "speed", 0.3, 2, 0.1),
                Slider("Length", Cfg.World.rain, "len", 6, 40, 1),
                Slider("Wind", Cfg.World.rain, "wind", -1, 1, 0.1),
                Toggle("Thunder Flashes", Cfg.World.rain, "thunder"),
            } },
        } },
        { name = "Screen", desc = "Color tint, vignette and dimming over the whole screen.", sections = {
            { title = "Color Tint", side = "left", items = {
                Toggle("Enabled", Cfg.World.tint, "enabled", { color = { Cfg.World.tint, "color" } }),
                Slider("Strength", Cfg.World.tint, "alpha", 0.02, 0.7, 0.01),
                Toggle("Rainbow", Cfg.World.tint, "rainbow"),
                Slider("Rainbow Speed", Cfg.World.tint, "rspeed", 0.05, 1, 0.05),
            } },
            { title = "Vignette", side = "right", items = {
                Toggle("Enabled", Cfg.World.vignette, "enabled"),
                Slider("Strength", Cfg.World.vignette, "alpha", 0.1, 1, 0.05),
            } },
            { title = "Dim", side = "right", items = {
                Toggle("Enabled", Cfg.World.dim, "enabled"),
                Slider("Strength", Cfg.World.dim, "alpha", 0.05, 0.8, 0.05),
            } },
        } },
    } },
    { name = "Skin Changer", short = "Skins", glyph = "skin", subs = {
        { name = "Weapons", desc = "Every weapon by loadout slot. Pick one to change its skin.", custom = function(x, y, w, h, dt) ExtSC.drawWeapons(x, y, w, h, dt) end },
        { name = "Cosmetics", desc = "Wraps, finishers and charms.", custom = function(x, y, w, h, dt) ExtSC.drawCosmetics(x, y, w, h, dt) end },
        { name = "Sky", desc = "Skybox pictures. Saved to the config and applied by the changer.", custom = function(x, y, w, h, dt) ExtSC.drawSkies(x, y, w, h, dt) end },
        { name = "Extras", desc = "Tracers, hands and hit sounds (saved to the same config).", sections = {
            { title = "Tracers", side = "left", items = {
                Drop("Color", XT, "color", TRACER_NAMES),
                Slider("Speed", XT, "speed", 5, 200, 5, "%"),
                Toggle("Energy Pistol Tracers", XT, "energy"),
            } },
            { title = "Hands", side = "left", items = {
                Toggle("Hide Hands (All Weapons)", XT, "hands"),
            } },
            { title = "Hit Sounds", side = "right", items = {
                Drop("Library", SND, "group", SND_GROUPS, refreshSounds),
                Drop("Body Hit", SND, "Hit", SND_OPTS, refreshSounds),
                Drop("Headshot", SND, "Critical", SND_OPTS, refreshSounds),
                Drop("Kill", SND, "Kill", SND_OPTS, refreshSounds),
            } },
            { title = "Apply", side = "right", items = {
                Button("Save & Apply", function() ExtSC.job("Applying...", ExtSC.apply) end),
                Stat("Status", function() return ExtSC.S.status, T.TextColor end),
            } },
        } },
        { name = "Settings", desc = "Lists and inventory.", sections = {
            { title = "Automation", side = "left", items = {
                Toggle("Auto Load", ExtSC, "autoLoad"),
                Toggle("Auto Apply In Game", ExtSC, "autoApply"),
                Button("Apply Skins Now", function() ExtSC.job("Applying...", ExtSC.apply) end),
                Stat("Status", function() return ExtSC.S.status, T.TextColor end),
            } },
            { title = "Lists", side = "right", items = {
                Toggle("Only Show What I Own", ExtSC, "ownedOnly"),
                Stat("Inventory", function() return ExtSC.invStatus(), T.TextColor end),
                Button("Reload Lists + Config", function() ExtSC.job("Reading...", function() ExtSC.loadConfig() ExtSC.loadCatalog() end) end),
            } },
        } },
    } },
    { name = "Gun Mods", glyph = "gun", subs = {
        { name = "Guns", desc = "Weapon stat overrides through Matcha's getgc / applygc. Untick a stat to leave it alone.", sections = {
            { title = "Stats", side = "left", items = {
                Toggle("Enable Gun Mods", Cfg.Gun, "enabled"),
                Toggle("Full Auto (Hold LMB)", Cfg.Gun, "fullAuto"),
                Slider("Full Auto Speed", Cfg.Gun, "autoDelay", 10, 100, 5, "ms"),
                Toggle("Recoil", Cfg.Gun, "recOn"),
                Slider("Recoil Value", Cfg.Gun, "recoil", 0, 5, 0.05),
                Toggle("Spread", Cfg.Gun, "sprOn"),
                Slider("Spread Value", Cfg.Gun, "spread", 0, 10, 0.05),
                Toggle("Accuracy", Cfg.Gun, "accOn"),
                Slider("Accuracy Value", Cfg.Gun, "accuracy", 0, 10, 0.05),
                Toggle("Fire Cooldown", Cfg.Gun, "cdOn"),
                Slider("Cooldown Value", Cfg.Gun, "cooldown", 0, 2, 0.005),
                Toggle("Projectile Speed", Cfg.Gun, "spdOn"),
                Slider("Speed Value", Cfg.Gun, "projSpeed", 0, 20000, 50),
            } },
            { title = "Control", side = "right", items = {
                Button("Set To Default", function()
                    Cfg.Gun.enabled, Cfg.Melee.enabled = false, false
                    ExtGun.restore()
                    ExtGun.wasOn = false
                end),
                Button("Rescan GC Memory", function() ExtGun.scan(true) end),
                Stat("Status", function() return ExtGun.status, T.TextColor end),
                Stat("Values Found", function() return tostring(ExtGun.found), T.TextColor end),
            } },
        } },
        { name = "Melee", desc = "Melee swing / recovery cooldown overrides.", sections = {
            { title = "Melee Cooldown", side = "left", items = {
                Toggle("Enabled", Cfg.Melee, "enabled"),
                Slider("Cooldown", Cfg.Melee, "cd", 0.001, 2, 0.001),
                Toggle("Include Generic Cooldown Keys", Cfg.Melee, "generic"),
                Button("Rescan GC Memory", function() ExtGun.scan(true) end),
                Stat("Status", function() return ExtGun.status, T.TextColor end),
                Button("Set To Default", function()
                    Cfg.Gun.enabled, Cfg.Melee.enabled = false, false
                    ExtGun.restore()
                    ExtGun.wasOn = false
                end),
            } },
        } },
    } },
    { name = "Settings", glyph = "gear", subs = {
        { name = "General", desc = "Menu, overlays, and diagnostics.", sections = {
            { title = "Menu", side = "left", items = {
                KeyRow("Menu Keybind", Cfg.Menu, "key"),
                KeyRow("Panic Key", Cfg.Menu, "panic"),
                Drop("Performance", Cfg.Menu, "performance", { "Ultra", "Middle", "Low" }),
                Toggle("Show Watermark", Cfg.Menu, "watermark"),
                Toggle("Show Keybind List", Cfg.Menu, "keylist"),
                Slider("Cursor Y Offset", Cfg.Menu, "yOffset", -60, 60, 1),
            } },
            { title = "Theme", side = "right", items = {
                Toggle("Accent", { v = true }, "v", { color = { Cfg.Menu, "accent" } }),
                Button("Copy Diagnostics", function() pcall(setclipboard, K.diag()) pcall(notify, "Diagnostics copied", "lolcat", 3) end),
                Button("Unload", function() K.Unload() end),
            } },
        } },
        { name = "Config", desc = "Save and load setting slots.", sections = {
            { title = "Config Profiles", side = "left", items = {
                Drop("Slot", Cfg.Menu, "slot", { "1", "2", "3", "4", "5" }),
                Button("Save", function() Store.save(Cfg.Menu.slot) end),
                Button("Load", function() Store.load(Cfg.Menu.slot) end),
                Button("Delete", function() Store.delete(Cfg.Menu.slot) end),
                Stat("Last Action", function() return Store.msg ~= "" and Store.msg or "-", T.TextColor end),
            } },
        } },
    } },
}
return P
end)()

-- layout helpers ------------------------------------------------------------
local ROW_H, PITCH = 24, 49
local function itemVisible(it) return it.show == nil or it.show() end
local function secVisibleCount(sec)
    local n = 0
    for _, it in ipairs(sec.items) do if itemVisible(it) then n = n + 1 end end
    return n
end
local function secHeight(sec)
    local n = secVisibleCount(sec)
    local box = 24
    if n > 0 then box = 24 + n * ROW_H + (n - 1) * (PITCH - ROW_H) end
    return 35 + box
end

local function fmtVal(it, v)
    if it.step >= 1 then return fmt("%d%s", floor(v + 0.5), it.suffix) end
    if it.step >= 0.1 then return fmt("%.1f%s", v, it.suffix) end
    if it.step >= 0.01 then return fmt("%.2f%s", v, it.suffix) end
    return fmt("%.3f%s", v, it.suffix)
end

-- popups ----------------------------------------------------------------------
function UI.openDrop(it, bx, by, bw)
    local rows = min(#it.opts, 12)
    local _, vh = viewport()
    UI.popup = { kind = "drop", it = it, x = bx, y = min(by + 26, vh - rows * 24 - 12), w = bw, h = rows * 24 + 8, rows = rows, off = 0, offf = 0, t = tick() }
end
function UI.openColor(tbl, key, sx, sy)
    local h, s, v = c2hsv(tbl[key])
    local w, hh = 196, 164
    UI.popup = { kind = "color", tbl = tbl, key = key, x = clamp(sx - w + 24, 4, 4000), y = sy + 28, w = w, h = hh, hue = h, sat = s, val = v }
end
local function colorGeom(p)
    return { sx = p.x + 8, sy = p.y + 8, sw = p.w - 16, sh = 112, hx = p.x + 8, hy = p.y + 128, hw = p.w - 16, hh = 22 }
end

function UI.popupInput()
    local p = UI.popup
    if not p then return end
    if p.kind == "drop" and #p.it.opts > p.rows then
        local nowT = tick()
        local dtp = clamp(nowT - (p.t or nowT), 0, 0.1)
        p.t = nowT
        local sp2 = 0
        if keyDown(0x28) then sp2 = 1 elseif keyDown(0x26) then sp2 = -1 end
        if I.inside(p.x, p.y + p.h - 20, p.w, 20) then sp2 = 1 elseif I.inside(p.x, p.y, p.w, 20) then sp2 = -1 end
        p.offf = clamp(p.offf + sp2 * 14 * dtp, 0, #p.it.opts - p.rows)
        p.off = floor(p.offf + 0.5)
    end
    if I.pressed then
        if I.inside(p.x, p.y, p.w, p.h) then
            if p.kind == "drop" then
                local idx = floor((I.my - p.y - 4) / 24) + 1 + (p.off or 0)
                if p.it.opts[idx] then p.it.tbl[p.it.key] = p.it.opts[idx] end
                UI.popup = nil
            else
                local g = colorGeom(p)
                if I.inside(g.sx, g.sy, g.sw, g.sh) then UI.active = { kind = "sv" }
                elseif I.inside(g.hx, g.hy, g.hw, g.hh) then UI.active = { kind = "hue" } end
            end
        else
            UI.popup = nil
        end
        I.pressed = false
    end
    if UI.popup and UI.popup.kind == "color" and UI.active and I.down and (UI.active.kind == "sv" or UI.active.kind == "hue") then
        local g = colorGeom(UI.popup)
        if UI.active.kind == "sv" then
            UI.popup.sat = clamp((I.mx - g.sx) / g.sw, 0, 1)
            UI.popup.val = 1 - clamp((I.my - g.sy) / g.sh, 0, 1)
        else
            UI.popup.hue = clamp((I.mx - g.hx) / g.hw, 0, 0.999)
        end
        UI.popup.tbl[UI.popup.key] = hsv2c(UI.popup.hue, UI.popup.sat, UI.popup.val)
    end
end

function UI.drawPopup()
    local p = UI.popup
    if not p then return end
    R.rect(p.x - 1, p.y - 1, p.w + 2, p.h + 2, T.Outline, 5)
    R.rect(p.x, p.y, p.w, p.h, T.ElementBackground, 5)
    if p.kind == "drop" then
        local cur = p.it.tbl[p.it.key]
        local off = p.off or 0
        for i = 1, p.rows do
            local o = p.it.opts[i + off]
            if o ~= nil then
                local ry = p.y + 4 + (i - 1) * 24
                local hover = I.inside(p.x, ry, p.w, 24)
                if hover then R.rect(p.x + 3, ry, p.w - 6, 24, mix(T.ElementBackground, T.TabButtonSelected, 0.4), 4) end
                local col = T.TextColor
                if o == cur then col = T.Accent end
                R.text(p.x + 12, ry + 4, tostring(o), 15, col, false)
            end
        end
        local total = #p.it.opts
        if total > p.rows then
            local th = max(18, (p.h - 8) * p.rows / total)
            R.rect(p.x + p.w - 5, p.y + 4 + (p.h - 8 - th) * off / (total - p.rows), 3, th, T.Accent, 1)
        end
    else
        local g = colorGeom(p)
        local cw, ch = g.sw / 14, g.sh / 8
        for cx = 0, 13 do
            for cy = 0, 7 do
                R.rect(g.sx + cx * cw, g.sy + cy * ch, ceil(cw) + 1, ceil(ch) + 1, hsv2c(p.hue, cx / 13, 1 - cy / 7))
            end
        end
        local mx2, my2 = g.sx + p.sat * g.sw, g.sy + (1 - p.val) * g.sh
        R.circle(mx2, my2, 5, T.White, false, 2, 16)
        local hw = g.hw / 24
        for i = 0, 23 do R.rect(g.hx + i * hw, g.hy, ceil(hw) + 1, g.hh, hsv2c(i / 24, 1, 1)) end
        R.rect(g.hx + p.hue * g.hw - 2, g.hy - 2, 4, g.hh + 4, T.White, 2)
        R.rect(p.x + 8, p.y + 156 - 2, 0, 0, 0)
    end
end

-- keybind capture ------------------------------------------------------------
function UI.captureTick()
    local cap = UI.capture
    if not cap then return end
    local anyDown = false
    for vk = 0x01, 0xFE do
        if keyDown(vk) then
            anyDown = true
            if cap.armed then
                if vk == 0x1B then cap.set(nil) else cap.set(vk) end
                UI.capture = nil
                return
            end
        end
    end
    if not anyDown then cap.armed = true end
end

-- item drawing -----------------------------------------------------------------
local function pill(x, y, a)
    local off = mix(T.ToggleBackgroundUnselected, T.GradientDark, 0.5)
    R.rect(x, y, 32, 20, mix(off, T.Accent, a), 10)
    R.rect(x + lerp(3, 13, a), y + 2, 16, 16, mix(T.ToggleCircleUnselected, T.White, a), 8)
end

local function ctrlBox(x, y, w, h, hover)
    R.rect(x - 1, y - 1, w + 2, h + 2, T.Outline, 6)
    R.rect(x, y, w, h, hover and T.GradientTop or T.GradientMid, 5)
end

local function bindText(b)
    local k = b.kind
    return fmt("%s: %s", k, keyName(b.key))
end

function UI.drawItem(it, x, y, w, vis, dt)
    local lbl = it.label
    local ts = 16
    local ty = y + 3
    if it.t == "divider" then
        if vis then
            local tw = R.tw(lbl, 13)
            local mid = x + w / 2
            R.rect(x, y + 11, mid - tw / 2 - 10 - x, 1, T.Outline)
            R.rect(mid + tw / 2 + 10, y + 11, x + w - (mid + tw / 2 + 10), 1, T.Outline)
            R.text(mid - tw / 2, y + 5, lbl, 13, T.Unselected, false)
        end
        return
    end
    if not vis then
        if it.t == "toggle" then
            local target = it.tbl[it.key] and 1 or 0
            it.a = target
        end
        return
    end

    if it.t == "toggle" then
        local v = it.tbl[it.key] and true or false
        local target = v and 1 or 0
        it.a = it.a + (target - it.a) * clamp(dt * 18, 0, 1)
        if abs(target - it.a) < 0.02 then it.a = target end
        local rx = x + w
        local px = rx - 32
        pill(px, y + 2, it.a)
        rx = px - 11
        local consumed = false
        if it.color then
            local sx = rx - 22
            R.rect(sx - 1, y, 24, 24, T.Outline, 6)
            R.rect(sx, y + 1, 22, 22, it.color[1][it.color[2]], 5)
            if I.pressed and I.inside(sx, y, 22, 24) and not UI.popup then
                UI.openColor(it.color[1], it.color[2], sx, y)
                I.pressed = false
                consumed = true
            end
            rx = sx - 11
        end
        if it.bind then
            local b = it.bind
            local txt = bindText(b)
            local tw = R.tw(txt, 13) + 16
            local bx = rx - tw
            local hover = I.inside(bx, y + 1, tw, 22)
            ctrlBox(bx, y + 1, tw, 22, hover)
            local capturing = UI.capture and UI.capture.bind == b
            R.text(bx + 8, y + 5, capturing and "press a key..." or txt, 13, capturing and T.Accent or T.TextColor, false)
            if not UI.popup then
                if I.pressed and hover then
                    UI.capture = { bind = b, armed = false, set = function(vk) b.key = vk end }
                    I.pressed = false
                    consumed = true
                elseif I.rpressed and hover then
                    if b.kind == "Always" then b.kind = "Toggle" elseif b.kind == "Toggle" then b.kind = "Hold" else b.kind = "Always" end
                    b.state = false
                    I.rpressed = false
                end
            end
        end
        R.text(x, ty, lbl, ts, T.TextColor, false)
        if not consumed and I.pressed and not UI.popup and I.inside(x, y, w, ROW_H) then
            it.tbl[it.key] = not v
            I.pressed = false
        end

    elseif it.t == "slider" then
        local v = it.tbl[it.key]
        local vtxt = fmtVal(it, v)
        local boxW = clamp(#vtxt * 16 * 0.55 + 14, 38, 76)
        local bx = x + w - boxW
        ctrlBox(bx, y + 1, boxW, 22, false)
        R.text(bx + (boxW - R.tw(vtxt, 14)) / 2, y + 4, vtxt, 14, T.TextColor, false)
        R.text(x, ty, lbl, ts, T.TextColor, false)
        local trackX = x + R.tw(lbl, ts) + 16
        local trackW = (bx - 11) - trackX
        if trackW < 30 then trackW = 30 end
        local frac = 0
        if it.max ~= it.min then frac = clamp((v - it.min) / (it.max - it.min), 0, 1) end
        R.rect(trackX, y + 11, trackW, 3, mix(T.Outline, T.GradientTop, 0.5), 1)
        R.rect(trackX, y + 11, max(1, trackW * frac), 3, T.Accent, 1)
        local dragging = UI.active and UI.active.it == it
        R.rect(trackX + trackW * frac - 7, y + 5, 14, 14, T.Accent, 7)
        R.rect(trackX + trackW * frac - 5, y + 7, 10, 10, dragging and T.Accent or T.White, 5)
        if I.pressed and not UI.popup and I.inside(trackX - 7, y, trackW + 14, ROW_H) then
            UI.active = { kind = "slider", it = it, tx = trackX, tw = trackW }
            I.pressed = false
        end

    elseif it.t == "drop" then
        local cur = tostring(it.tbl[it.key])
        local maxw = 0
        for _, o in ipairs(it.opts) do maxw = max(maxw, R.tw(tostring(o), 15)) end
        local boxW = clamp(maxw + 38, 96, 190)
        local bx = x + w - boxW
        local hover = I.inside(bx, y + 1, boxW, 22)
        local isOpen = UI.popup and UI.popup.it == it
        ctrlBox(bx, y + 1, boxW, 22, hover or isOpen)
        R.text(bx + 9, y + 4, cur, 15, T.TextColor, false)
        local ax, ay = bx + boxW - 14, y + 11
        R.line(ax - 4, ay - 2, ax, ay + 2, T.Unselected, 1.5)
        R.line(ax, ay + 2, ax + 4, ay - 2, T.Unselected, 1.5)
        R.text(x, ty, lbl, ts, T.TextColor, false)
        if I.pressed and hover and not UI.popup then
            UI.openDrop(it, bx, y + 1, boxW)
            I.pressed = false
        end

    elseif it.t == "button" then
        local hover = I.inside(x, y + 1, w, 22)
        ctrlBox(x, y + 1, w, 22, hover)
        R.text(x + (w - R.tw(lbl, 15)) / 2, y + 4, lbl, 15, hover and T.Accent or T.TextColor, false)
        if I.pressed and hover and not UI.popup then
            I.pressed = false
            if it.fn then pcall(it.fn) end
        end

    elseif it.t == "stat" then
        local s, col = it.get()
        s = tostring(s)
        R.text(x, ty, lbl, ts, T.TextColor, false)
        R.text(x + w - R.tw(s, 15), y + 4, s, 15, col or T.TextColor, false)

    elseif it.t == "keyrow" then
        local txt = keyName(it.tbl[it.key])
        local capturing = UI.capture and UI.capture.tbl == it
        if capturing then txt = "press a key..." end
        local tw = R.tw(txt, 14) + 18
        local bx = x + w - tw
        local hover = I.inside(bx, y + 1, tw, 22)
        ctrlBox(bx, y + 1, tw, 22, hover)
        R.text(bx + 9, y + 4, txt, 14, capturing and T.Accent or T.TextColor, false)
        R.text(x, ty, lbl, ts, T.TextColor, false)
        if I.pressed and hover and not UI.popup then
            UI.capture = { tbl = it, armed = false, set = function(vk) it.tbl[it.key] = vk or 0 end }
            I.pressed = false
        end
    end
end

-- main window ------------------------------------------------------------------
function UI.draw(dt)
    if not UI.open then UI.popup = nil UI.active = nil UI.drag = nil UI.capture = nil return end
    local vw, vh = viewport()
    if not UI.x then UI.x = floor((vw - WIN_W) / 2); UI.y = floor((vh - WIN_H) / 2) end
    UI.x = clamp(UI.x, 0, max(0, vw - WIN_W))
    UI.y = clamp(UI.y, 0, max(0, vh - WIN_H))

    UI.captureTick()
    UI.popupInput()

    -- slider drag
    local act = UI.active
    if act and act.kind == "slider" then
        if I.down then
            local it = act.it
            local f = clamp((I.mx - act.tx) / act.tw, 0, 1)
            local v = it.min + f * (it.max - it.min)
            v = round(v / it.step) * it.step
            it.tbl[it.key] = clamp(v, it.min, it.max)
        else
            UI.active = nil
        end
    elseif act and (act.kind == "sv" or act.kind == "hue") and not I.down then
        UI.active = nil
    end

    -- window drag
    if I.pressed and not UI.popup and not UI.active and I.inside(UI.x, UI.y, WIN_W, OUTER + HEAD_H) then
        UI.drag = { I.mx - UI.x, I.my - UI.y }
        I.pressed = false
    end
    if UI.drag then
        if I.down then
            UI.x = clamp(I.mx - UI.drag[1], 0, max(0, vw - WIN_W))
            UI.y = clamp(I.my - UI.drag[2], 0, max(0, vh - WIN_H))
            UI.popup = nil
        else
            UI.drag = nil
        end
    end
    local x, y = UI.x, UI.y

    -- shell
    R.rect(x - 1, y - 1, WIN_W + 2, WIN_H + 2, T.Outline, 6)
    R.rect(x, y, WIN_W, WIN_H, T.Background, 5)

    -- rail
    R.vgrad(x + 1, y + 1, RAIL_W, HEAD_H, T.GradientTop, T.GradientMid, 8)
    R.vgrad(x + 1, y + 1 + HEAD_H, RAIL_W, WIN_H - 2 - HEAD_H, T.GradientMid, T.GradientDark, 16)
    R.rect(x + RAIL_W + 1, y + 1, 1, WIN_H - 2, T.Outline)
    local logo = "LOLCAT"
    R.text(x + 1 + (RAIL_W - R.tw(logo, 20)) / 2, y + 30, logo, 20, T.Accent, true)
    R.rect(x + 1, y + HEAD_H, RAIL_W, 1, T.Accent)
    R.rect(x + 1, y + HEAD_H + 1, RAIL_W, 1, mix(T.Accent, T.GradientMid, 0.65))
    R.rect(x + 1, y + HEAD_H + 2, RAIL_W, 1, mix(T.Accent, T.GradientMid, 0.88))

    for i, pg in ipairs(Pages) do
        local tx, ty = x + 1 + (RAIL_W - 66) / 2, y + 98 + (i - 1) * 57
        local sel = (UI.tab == i)
        local hover = I.inside(tx, ty, 66, 54)
        if sel then
            R.rect(tx, ty, 66, 54, T.TabShadow, 6)
            R.rect(tx, ty, 66, 38, T.TabButtonSelected, 6)
            R.rect(tx, ty + 24, 66, 16, mix(T.TabButtonSelected, T.TabShadow, 0.5))
        elseif hover then
            R.rect(tx, ty, 66, 54, mix(T.GradientMid, T.TabButtonSelected, 0.25), 6)
        end
        local col = sel and T.Accent or (hover and T.TextColor or T.Unselected)
        Glyph[pg.glyph](tx + 33, ty + 19, col)
        local nm = pg.short or pg.name
        R.text(tx + (66 - R.tw(nm, 11)) / 2, ty + 37, nm, 11, col, true)
        if I.pressed and hover and not UI.popup then
            UI.tab = i
            I.pressed = false
        end
    end

    -- page header
    local page = Pages[UI.tab]
    local subIdx = clamp(UI.sub[UI.tab] or 1, 1, #page.subs)
    local sub = page.subs[subIdx]
    local px = x + RAIL_W + OUTER
    R.text(px, y + OUTER + 18, page.name, 18, T.TextColor, true)
    R.text(px, y + OUTER + 44, sub.desc or "", 13, T.Unselected, false)

    local gridTop = y + OUTER + HEAD_H
    if #page.subs > 1 then
        local cx = px
        local sy = y + OUTER + HEAD_H + 17
        for i, sb in ipairs(page.subs) do
            local w = 32 + R.tw(sb.name, 16)
            local sel = (i == subIdx)
            local hover = I.inside(cx, sy, w, 50)
            if sel then
                R.rect(cx, sy, w, 50, mix(T.GradientMid, T.TabButtonSelected, 0.3), 6)
                R.rect(cx + 10, sy + 46, w - 20, 2, T.Accent, 1)
            end
            R.text(cx + 16, sy + 15, sb.name, 16, sel and T.Accent or (hover and T.TextColor or T.Unselected), true)
            if I.pressed and hover and not UI.popup then
                UI.sub[UI.tab] = i
                subIdx = i
                sub = sb
                I.pressed = false
            end
            cx = cx + w + 14
        end
        gridTop = y + OUTER + HEAD_H + STRIP_H
    end

    -- grid
    local gridBottom = y + WIN_H - 17
    local gridLeft, gridRight = px, x + WIN_W - OUTER
    local colW = floor((gridRight - gridLeft - GAPX) / 2)
    local viewH = gridBottom - gridTop
    if sub.custom then
        R.clip = { gridLeft, gridTop, gridRight, gridBottom }
        local okc, errc = pcall(sub.custom, gridLeft, gridTop, gridRight - gridLeft, viewH, dt)
        R.clip = nil
        K.errors.customPage = (not okc) and tostring(errc) or nil
        UI.drawPopup()
        return
    end
    local h1, h2 = 0, 0
    for _, sec in ipairs(sub.sections) do
        local hh = secHeight(sec)
        if sec.side == "right" then h2 = h2 + hh + GAPX else h1 = h1 + hh + GAPX end
    end
    local contentH = max(h1, h2) - GAPX
    local maxScroll = max(0, contentH - viewH)
    local skey = UI.tab * 100 + subIdx
    local scroll = clamp(UI.scroll[skey] or 0, 0, maxScroll)
    if I.inside(gridLeft, gridTop, gridRight - gridLeft, viewH) and not UI.popup then
        if keyDown(0x28) then scroll = scroll + 700 * dt end
        if keyDown(0x26) then scroll = scroll - 700 * dt end
    end
    -- scrollbar
    if maxScroll > 0 then
        local thumbH = max(30, viewH * viewH / contentH)
        local thumbY = gridTop + (viewH - thumbH) * (scroll / maxScroll)
        local sx = gridRight + 6
        R.rect(sx, gridTop, 4, viewH, T.GradientTop, 2)
        R.rect(sx, thumbY, 4, thumbH, T.Accent, 2)
        if I.pressed and not UI.popup and I.inside(sx - 6, gridTop, 16, viewH) then
            UI.active = { kind = "scroll", off = I.my - thumbY, key = skey }
            I.pressed = false
        end
        if UI.active and UI.active.kind == "scroll" and UI.active.key == skey then
            if I.down then
                local f = clamp((I.my - UI.active.off - gridTop) / (viewH - thumbH), 0, 1)
                scroll = f * maxScroll
            else
                UI.active = nil
            end
        end
    end
    scroll = clamp(scroll, 0, maxScroll)
    UI.scroll[skey] = scroll

    R.clip = { gridLeft, gridTop, gridRight, gridBottom }
    local cy1, cy2 = gridTop - scroll, gridTop - scroll
    for _, sec in ipairs(sub.sections) do
        local right = (sec.side == "right")
        local sx = right and (gridLeft + colW + GAPX) or gridLeft
        local sy
        if right then sy = cy2 else sy = cy1 end
        local n = secVisibleCount(sec)
        local boxH = 24
        if n > 0 then boxH = 24 + n * ROW_H + (n - 1) * (PITCH - ROW_H) end
        R.text(sx + 1, sy, sec.title, 16, T.TextColor, true)
        local by = sy + 35
        R.rect(sx, by, colW, boxH, T.Outline, 6)
        R.rect(sx + 1, by + 1, colW - 2, boxH - 2, T.ElementBackground, 5)
        local iy = by + 12
        local idx = 0
        for _, it in ipairs(sec.items) do
            if itemVisible(it) then
                idx = idx + 1
                local vis = iy >= gridTop and iy + ROW_H <= gridBottom and I.inside(gridLeft, gridTop, gridRight - gridLeft, viewH)
                local visDraw = iy >= gridTop and iy + ROW_H <= gridBottom
                -- interactions are only live while the row is fully inside the clip and the mouse is in the grid
                local saveP, saveR = I.pressed, I.rpressed
                if not I.inside(gridLeft, gridTop, gridRight - gridLeft, viewH) then I.pressed = false; I.rpressed = false end
                UI.drawItem(it, sx + 12, iy, colW - 24, visDraw, dt)
                if not I.inside(gridLeft, gridTop, gridRight - gridLeft, viewH) then I.pressed = saveP; I.rpressed = saveR end
                if idx < n then R.rect(sx + 12, iy + ROW_H + 12, colW - 24, 1, T.Outline) end
                iy = iy + PITCH
            end
        end
        local nextY = sy + 35 + boxH + GAPX
        if right then cy2 = nextY else cy1 = nextY end
    end
    R.clip = nil

    UI.drawPopup()
end

--------------------------------------------------------------------------
-- overlays: watermark + keybind list
--------------------------------------------------------------------------
local function drawOverlays()
    local m = Cfg.Menu
    local vw = viewport()
    if m.watermark then
        local ping = try(GetPingValue)
        local s = fmt("lolcat  |  matcha  |  %d fps  |  %s ms", floor(fpsAvg), ping and tostring(floor(ping)) or "?")
        local w = R.tw(s, 14) + 20
        local x, y = vw - w - 14, 14
        R.rect(x - 1, y - 1, w + 2, 28, T.Outline, 5)
        R.rect(x, y, w, 26, T.ElementBackground, 4)
        R.rect(x, y, w, 2, T.Accent, 1)
        R.text(x + 10, y + 6, s, 14, T.TextColor, false)
    end
    if m.keylist then
        local rows = {}
        for _, b in ipairs(allBinds) do
            if b.name and b.owner and b.owner.enabled and b.kind ~= "Always" and b.active then rows[#rows + 1] = b end
        end
        if #rows > 0 then
            local w = 150
            local x, y = 14, 300
            R.rect(x - 1, y - 1, w + 2, 30 + #rows * 20, T.Outline, 5)
            R.rect(x, y, w, 28 + #rows * 20, T.ElementBackground, 4)
            R.rect(x, y, w, 2, T.Accent, 1)
            R.text(x + 10, y + 6, "Keybinds", 14, T.TextColor, true)
            for i, b in ipairs(rows) do
                R.text(x + 10, y + 12 + i * 20, b.name, 13, T.TextColor, false)
                local t = "[" .. b.kind .. "]"
                R.text(x + w - 10 - R.tw(t, 13), y + 12 + i * 20, t, 13, T.Accent, false)
            end
        end
    end
end

--------------------------------------------------------------------------
-- main loop
--------------------------------------------------------------------------
local function guard(name, f, ...)
    local ok, err = pcall(f, ...)
    if not ok then
        if not K.errors[name] then K.errorCount = K.errorCount + 1 end
        K.errors[name] = tostring(err)
    else
        K.errors[name] = nil
    end
end

-- Opening the menu stops Roblox from receiving mouse / keyboard input and asks it to release a
-- locked (first-person) cursor, so the menu is usable in shooters. Each step is optional.
local inputGrabbed, unlockT = nil, 0
function K.setMenuInput(open)
    if open ~= inputGrabbed then
        inputGrabbed = open
        if type(setrobloxinput) == "function" then pcall(setrobloxinput, not open) end
    end
    if open and tick() - unlockT > 0.1 then
        unlockT = tick()
        pcall(function()
            local uis = game:GetService("UserInputService")
            uis.MouseBehavior = Enum.MouseBehavior.Default
            uis.MouseIconEnabled = true
        end)
    end
end

local menuPrev, panicPrev = false, false
function K.panic()
    Cfg.Aimbot.enabled = false
    Cfg.Ragebot.enabled = false
    Cfg.Trigger.enabled = false
    Cfg.Movement.fly.enabled = false
    Cfg.Movement.speed.enabled = false
    Cfg.Movement.noclip.enabled = false
    Cfg.Silent.enabled = false
    Cfg.Gun.enabled = false
    Cfg.Melee.enabled = false
    pcall(notify, "All combat / movement features disabled", "lolcat panic", 3)
end

K.last = tick()
function K.frame()
    if not K.alive then return end
    local now = tick()
    local dt = clamp(now - K.last, 0.001, 0.1)
    K.last = now
    fpsAvg = lerp(fpsAvg, 1 / dt, 0.08)
    T.Accent = Cfg.Menu.accent

    I.update()
    for _, b in ipairs(allBinds) do evalBind(b) end

    local md = keyDown(Cfg.Menu.key)
    if md and not menuPrev then UI.open = not UI.open end
    menuPrev = md
    local pd = keyDown(Cfg.Menu.panic)
    if pd and not panicPrev then K.panic() end
    panicPrev = pd

    guard("input", Ext.TI.tick)
    guard("links", Ext.linkTick)
    guard("targets", Targets.refresh)
    guard("world", World.tick)
    guard("lighting", ExtLit.tick)
    guard("gun", ExtGun.tick)
    guard("rage", Rage.tick)
    guard("silent", ExtSA.tick)
    guard("aim", Aim.tick)
    guard("trigger", Trig.tick)
    guard("move", Move.tick, dt)

    guard("worldfx", ExtFX.draw, dt)
    guard("esp", Esp.draw)
    guard("silentfov", ExtSA.draw)
    guard("crosshair", drawCrosshair)
    guard("fov", drawFov)
    guard("overlay", drawOverlays)
    guard("ui", UI.draw, dt)
    -- own cursor dot while the menu is open (the real one may be locked by the game)
    if UI.open then
        R.circle(I.mx, I.my, 4, T.Black or 0, true, 1, 12)
        R.circle(I.mx, I.my, 3, T.Accent, true, 1, 12)
    end
    R.flush()
    K.setMenuInput(UI.open)
end

function K.Unload()
    if not K.alive then return end
    K.alive = false
    pcall(Rage.disengage, myParts())
    pcall(World.restore)
    pcall(function()
        local root = myParts()
        if root then root.AssemblyLinearVelocity = Vector3.new(0, 0, 0) end
    end)
    pcall(ExtSA.restore)
    pcall(ExtLit.restoreAll)
    pcall(function() if Cfg.Gun.enabled or Cfg.Melee.enabled or ExtGun.wasOn then ExtGun.restore() end end)
    pcall(function() if type(setrobloxinput) == "function" then setrobloxinput(true) end end)
    R.destroy()
end

-- Optional auto-load of slot 1 if present
pcall(function()
    if isfile(slotPath("auto")) then deser(Cfg, HttpService:JSONDecode(readfile(slotPath("auto")))) end
end)

task.spawn(function()
    while K.alive do
        K.frame()
        task.wait()
    end
end)

pcall(notify, "lolcat (Matcha) loaded - press RightShift to toggle the menu", "lolcat", 5)
