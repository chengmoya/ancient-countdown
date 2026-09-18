#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
古风倒计时 · Ancient Countdown
================================
极低资源占用的桌面倒计时小工具

设计目标
  · 空闲 CPU  ≈ 0%      —— 不使用死循环，按「对齐到下一秒」的方式调度，每秒仅一次轻量重绘
  · 内存占用  ≈ 20 MB   —— Tk 原生窗口，无浏览器内核 / 无 Electron
  · 冷启动    < 0.5 s   —— 单文件脚本，无第三方依赖

功能
  1. 目标时间解析        支持 "10.1.11.30" 这类简洁写法（月.日.时.分）
  2. 大字号倒计时        天 / 時 / 分 / 秒
  3. 窗口尺寸            可锁定固定大小，也可拖拽任意边缘自由缩放
  4. 颜色规则            多档阈值，剩余时间越少颜色越紧迫，可自定义前景色与底色
  5. 归零提示            「時辰已到」闪烁
  6. 古风画风            宣纸底 · 古铜双框 · 朱砂印 · 楷体

操作
  拖动窗口内部  = 移动窗口        拖动窗口边缘 = 缩放窗口
  双击 / 点击右上「設」 = 打开设置      右键 = 菜单
"""

import datetime
import glob
import hashlib
import json
import os
import random
import re
import shutil
import sys
import time
import winreg
import tkinter as tk
from tkinter import filedialog
from tkinter import font as tkfont
from tkinter import messagebox

# --------------------------------------------------------------------------
# 常量
# --------------------------------------------------------------------------

APP_NAME = "古风倒计时"
APP_SUB = "ANCIENT COUNTDOWN"

# 当前版本号，与 version.json 里的 version、Release 的 tag 三者对应。
# 在线升级靠它判断「有没有新版」：两边都是 "主.次" 两段数字，
# 比较时拆成 (1, 3) 这样的小元组比大小 —— 字符串比会出事，
# "1.10" < "1.9" 在字符串世界里是成立的，那会让用户升不上去。
APP_VERSION = "1.6"

MIN_W, MIN_H = 300, 150          # 窗口最小尺寸
# 数字字号的下限。宁可让它稍微顶出一点，也不缩到看不清：
# 这个挂件的全部用途就是那一串数字，缩成蚂蚁大小等于没用。
MIN_NUM_SIZE = 12
RESIZE_MARGIN = 9                # 边缘拖拽感应带宽度(px)
TICK_IDLE_MS = 600               # 归零状态闪烁间隔
MIN_VISIBLE_W, MIN_VISIBLE_H = 140, 70   # 窗口在桌面内的最小露出尺寸，不足即视为「跑到屏幕外」

# 右上角三个按钮（設 / — / ✕）的命中框与圆心间距。
# 窗口是无边框的，按钮只能自己画、自己判命中，所以这里定死一套尺寸：
# CTRL_HIT 是「离圆心这么近就算点中」，宁可稍微宽松一点，手指头不必点准圆心；
# CTRL_STEP_MIN 是两枚按钮圆心之间的最小距离，窗口再小也不许更挤 ——
# 必须**严格大于 2×CTRL_HIT**，否则两枚按钮的命中框会搭在一起：
# 手指落在夹缝里会同时压中两个按钮，而「✕」就在最外侧，
# 一次误触直接退出程序 —— 这种代价不能靠「应该点不准」来赌。
CTRL_HIT = 12
CTRL_STEP_MIN = 30

# 单实例名后面会拼上数据目录的路径指纹（见 acquire_single_instance）：
# 这样「演练实例」和「真正在用的实例」互不干扰，否则跑一次自检就会
# 让真程序以为「已经有一个在跑了」，其实是它自己把门堵上。
MUTEX_NAME = "Local\\AncientCountdown_SingleInstance"
WAKE_FILE = "_wake.signal"       # 第二个实例留下的「请现身」信号

# ---- 开机自动运行 ----
# 写在 HKCU 的 Run 键里：只影响当前用户，不需要管理员权限，
# 卸载时也只需删掉这一个值。勾选框的状态永远以注册表为准（见 is_autostart_on）。
AUTOSTART_RUN_PATH = r"Software\Microsoft\Windows\CurrentVersion\Run"
AUTOSTART_VALUE_NAME = "AncientCountdown"

# ---- 飞书传信（邮件通知）----
# 核心原则：发信一律派生独立进程去做。smtplib 导入要几 MB，
# 网络请求最长可阻塞 20 秒——放进主进程等于给常驻开销和界面流畅度找麻烦。
NOTIFY_CHECK_SEC = 30            # 巡检间隔：每 30 秒最多判断一次，进一步压低开销
NOTIFY_RETRY_SEC = 600           # 发信失败后隔多久重试
NOTIFY_MAX_RETRY = 3             # 同一条规则最多重试几次
NOTIFY_SENDING_TIMEOUT = 180     # 「发送中」超过这个秒数视为发信进程已死，允许重试
NOTIFY_BODY_LIMIT = 4000         # 邮件正文上限（字节），防意外超长
SIGNATURE_LIMIT = 24             # 本机抬头最大字数：它要进主题，太长会把标题挤爆

MAILER_FILE = "mailer.pyw"
NOTIFY_TASK_FILE = "notify_task.json"
NOTIFY_RESULT_FILE = "notify_result.json"
NOTIFY_TEST_RESULT_FILE = "notify_test_result.json"
NOTIFY_STATE_FILE = "notify_state.json"
NOTIFY_SECRET_FILE = "notify_secret.json"

# ---- 多机共用设置 ----
#
# 场景：十来台机器要配一模一样的颜色、传书设置，只有「本机抬头」和
# 「目标时刻」刻意各不相同。做法是把设置导出成一份文件，挨台机器喂一次：
#
#   A 机调好 → 设置面板「导出共用设置…」→ 挑好带哪些项 → 得一个 共用设置.json
#   → 拷到 B 机 → B 机上打开设置面板「从文件导入…」选中它 → 当场生效
#
# 导入**必须手动**，这一点是用户明确定的（v1.6 改掉的第一版做法）：
# 早期做成「启动时扫 exe 旁边、有就读走并删掉」，听着省事，实际很危险 ——
#   · 只要那份文件还在（比如拷过来还没来得及启、或者启了但没读成），
#     每一次启动都会再覆盖一遍，这台机器上独有的设置永远留不住；
#   · 出了事用户根本想不到是「旁边那个文件」干的，排查方向完全错。
# 改成手动挑文件之后，什么时候导、导哪一份，都是当场看见、当场决定的；
# 而且不删用户那份文件 —— 他很可能就是留着当母本的。
#
# 导出时还能一项一项挑（见 SHARED_ITEMS）：没勾的那一项根本不进文件，
# 也就不可能覆盖对方机器上那一项。
SHARED_FILE = "共用设置.json"
SHARED_SCHEMA = 1
# 这几个键名都指注册表里的值，不是用户配置：
#   shared_last      最近一次导入的结果（设置面板里显示给用户看）
#   shared_error     最近一次导入失败的原因（同样是给人看的）
SHARED_LAST_KEY = "shared_last"
SHARED_ERR_KEY = "shared_error"

# ---- 在线升级 ----
#
# 版本信息是一份小 JSON（约 600 字节），放在 CNB 上一个 tag 固定为
# update-info 的 Release 附件里。为什么绕这一下：
#   · CNB 的 API、以及仓库文件的直读，**都必须登录**（匿名一律 401）；
#     只有 Release 的附件是免登录可下的（实测 200）。
#   · 于是把「版本号 + 下载地址 + sha256」做成一个附件，程序直接下载它，
#     查询和下载就都走国内，不碰 GitHub。
#   · tag 固定，所以 URL 永远不变；每次发版只覆盖附件内容。
# 备用通道走 GitHub 的 Release API（匿名可读），万一 CNB 不可达还能查。
# 演练开关：端到端测试需要一个「完全不碰线上」的版本来源，指哪儿读哪儿。
# 平时这个环境变量不存在，就走下面的正式地址；只有测试进程里才设它。
UPDATE_INFO_CNB = (os.environ.get("ANCIENT_COUNTDOWN_UPDATE_INFO")
                   or "https://cnb.cool/chengmoCNB/ancient-countdown"
                      "/-/releases/download/update-info/version.json")
UPDATE_INFO_GITHUB_API = ("https://api.github.com/repos/chengmoya"
                          "/ancient-countdown/releases/latest")
UPDATE_FALLBACK_CNB = ("https://cnb.cool/chengmoCNB/ancient-countdown"
                       "/-/releases/download/%s/AncientCountdown_%s.zip")
UPDATE_CONNECT_TIMEOUT = 12      # 连不上就别让用户干等
UPDATE_MAX_INFO_BYTES = 200000   # 版本信息不可能超过这个数，防异常响应
UPDATE_OLD_SUFFIX = ".old"       # 旧 exe 被改名后的后缀（保留以便回滚）

# ---- 自动检查更新（静默，绝不打扰）----
#
# 这一套的底线是：**它出任何问题都不能影响倒计时本身**。
# 所以查询失败一律静默吞掉（不弹窗、不在界面上写错误文字），
# 而且只在「距上次真查过 ≥ 7 天」时才碰网络 —— 绝大多数巡检
# 只是一次减法，连注册表都不用读。
UPDATE_CHECK_KEY = "update_check"        # 自动检查的状态（存注册表）
UPDATE_AUTO_START_DELAY = 60             # 启动后静置多少秒才开始自动检查
UPDATE_AUTO_SCAN_SEC = 6 * 3600          # 巡检间隔：每 6 小时醒一次看看该不该查
UPDATE_CHECK_MIN_GAP = 7 * 86400         # 两次真查询之间至少隔 7 天

# ---- 更新后的「可回滚窗口」----
#
# .old 是用户唯一的回滚手段，所以不能新版本一启动就删：
# 用户说的「新版有问题」往往不是「起不来」（起不来时这段代码根本跑不到），
# 而是「起来了但功能不对」—— 那种情况下 .old 要是已经没了，想退都退不回去。
UPDATE_GUARD_KEY = "update_guard"        # 更新后的成功启动计数（存注册表）
UPDATE_GUARD_RUNS = 3                    # 稳定启动满几次才把 .old 删掉
UPDATE_GUARD_DELAY_MS = 60 * 1000        # 启动后满多久才算「这一次启动成功了」

# 常见邮箱的 SMTP 参数：(显示名, 服务器, 端口, 是否 SSL)
# 选服务商只填邮箱地址和授权码即可，服务器参数自动带出
SMTP_PROVIDERS = [
    ("QQ 邮箱",     "smtp.qq.com",        465, True),
    ("QQ 企业邮箱", "smtp.exmail.qq.com",  465, True),
    ("163 邮箱",    "smtp.163.com",       465, True),
    ("126 邮箱",    "smtp.126.com",       465, True),
    ("新浪邮箱",    "smtp.sina.com",      465, True),
    ("阿里云邮箱",  "smtp.aliyun.com",    465, True),
    ("Gmail",       "smtp.gmail.com",     465, True),
    ("Outlook",     "smtp.office365.com", 587, False),
    ("自定义",      "",                   465, True),
]
PROVIDER_NAMES = [p[0] for p in SMTP_PROVIDERS]

# 古风预设色板（设置面板中的调色选项）
PRESET_COLORS = [
    ("朱砂", "#B03A2E"), ("胭脂", "#D9707F"), ("琥珀", "#C08A1E"),
    ("鎏金", "#D9A13B"), ("竹青", "#4F7A52"), ("松绿", "#3E7C6A"),
    ("靛蓝", "#3E6E9E"), ("黛紫", "#7B5EA7"), ("墨黑", "#2B2622"),
    ("玄灰", "#6B5F52"), ("月白", "#F2EFE4"), ("素笺", "#EFE4CE"),
]

DEFAULT_CONFIG = {
    "target": "10.1.11.30",
    "locked": False,             # 锁定窗口尺寸
    "always_on_top": True,
    "autostart": False,          # 开机自动运行（真实状态以注册表为准，此为笔录）
    # 自动检查新版本：默认开着，但用户可以随时在设置面板里关掉。
    # 关掉之后程序不会再主动联网，只剩手动点「检查更新」这一条路。
    "auto_update_check": True,
    "window": {"x": None, "y": None, "w": 620, "h": 300},

    "palette": {
        "paper":       "#EFE4CE",   # 宣纸底
        "paper_night": "#1C1A17",   # 夜色底（紧急状态用）
        "ink":         "#2B2622",   # 墨
        "ink_soft":    "#6B5F52",   # 淡墨
        "border":      "#8C6B4A",   # 古铜框
        "border_soft": "#C4A87C",   # 浅铜框
        "seal":        "#B03A2E",   # 朱砂
        "default_fg":  "#3A322A",   # 常态字色
    },

    # 颜色规则：剩余时间 <= days 天时，切换到 color（底色 bg 可选）
    # 数组顺序无关，程序自动按 days 从小到大匹配「最紧迫」的一条
    "thresholds": [
        {"days": 7.0,  "color": "#4F7A52", "bg": None, "label": "一周内"},
        {"days": 4.0,  "color": "#C08A1E", "bg": None, "label": "四天内"},
        {"days": 2.0,  "color": "#B03A2E", "bg": None, "label": "两日内"},
        {"days": 0.5,  "color": "#F2EFE4", "bg": "#1C1A17", "label": "最后半日"},
    ],

    "zero_text": "時辰已到",
    "zero_color": "#B03A2E",
    "zero_color_alt": "#D9A13B",

    # 鸿雁传书：剩余时间跨过某一档时，寄一封邮件给你
    # 授权码不在这里 —— 单独存在 notify_secret.json，
    # 这样你把配置分享给别人时不会连密码一起带出去。
    "notify": {
        "enabled": False,
        "provider": "QQ 邮箱",
        "host": "smtp.qq.com",
        "port": 465,
        "use_ssl": True,
        "user": "",                 # 发件邮箱（同时是 SMTP 登录账号）
        "to": "",                   # 收件邮箱；留空 = 发给自己
        # 本机抬头：多台电脑都装了这个小工具时，用来分辨信是哪台寄的。
        # 会同时出现在「发件人显示名」「主题前缀」「正文落款」三处，
        # 前两处不用点开邮件就能看见。留空 = 不加抬头。
        # 首次运行会自动种入计算机名，想改成「书房台机」这样更好记的再改。
        "signature": "",
        "rules": [                  # 可自由增删；days 支持小数，0.5 即 12 小时
            {"days": 2.0, "enabled": True, "label": "剩两日"},
            {"days": 0.5, "enabled": True, "label": "最后半日"},
            {"days": 0.0, "enabled": True, "label": "时辰已到"},
        ],
    },
}

# 古风文字表
# ⚠ CN_MONTHS / CN_DAYS 已停用，保留只为存档，**不要拿去渲染日期**。
#
# 停用原因（2026-09-18 实测）：这套「正月 / 冬月 / 腊月 / 初一 / 廿五」是农历的
# 专用叫法，套在公历上会让人以为倒计时算错了——公历 12 月 25 日被显示成
# 「腊月廿五」，而真正的农历腊月廿五在另一个月份。现改用 pretty_target() 的
# 数字写法。
#
# 另一个致命点：CN_DAYS 只到「三十」（共 31 项，下标 0~30），
# **任何 31 号都会 IndexError**，包括 12.31 跨年倒计时。若哪天要恢复古风写法，
# 必须先把这张表补到 31 日，并把 1/3/5/7/8/10/12 月的 31 号纳入单测。
CN_MONTHS = ["正月", "二月", "三月", "四月", "五月", "六月",
             "七月", "八月", "九月", "十月", "冬月", "腊月"]
CN_DAYS = ["", "初一", "初二", "初三", "初四", "初五", "初六", "初七", "初八", "初九", "初十",
           "十一", "十二", "十三", "十四", "十五", "十六", "十七", "十八", "十九", "二十",
           "廿一", "廿二", "廿三", "廿四", "廿五", "廿六", "廿七", "廿八", "廿九", "三十"]
CN_SHICHEN = ["子", "丑", "寅", "卯", "辰", "巳", "午", "未", "申", "酉", "戌", "亥"]
CN_NUMS = "〇一二三四五六七八九"


# --------------------------------------------------------------------------
# 工具函数
# --------------------------------------------------------------------------

def screen_rect(root=None):
    """
    返回「虚拟桌面」（含所有显示器）的范围 (left, top, right, bottom)。

    为什么不用 Tk 自带的 winfo_screenwidth？因为它只认主显示器：
    窗口放到副屏、或副屏被拔掉之后，坐标会被算错，窗口就会跑到看不见的地方。
    这里优先向系统要整个虚拟桌面的范围，拿不到再退回主屏尺寸。
    """
    try:
        import ctypes
        g = ctypes.windll.user32.GetSystemMetrics
        left, top = g(76), g(77)          # SM_XVIRTUALSCREEN / SM_YVIRTUALSCREEN
        width, height = g(78), g(79)      # SM_CXVIRTUALSCREEN / SM_CYVIRTUALSCREEN
        if width > 0 and height > 0:
            return left, top, left + width, top + height
    except Exception:
        pass
    if root is not None:
        return 0, 0, root.winfo_screenwidth(), root.winfo_screenheight()
    return 0, 0, 1920, 1080


def hwnd_of(widget):
    """
    Tk 部件对应的 Windows 顶层窗口句柄。

    取不到时返回 0 —— 调用方据此回退到 Tk 自己的路子，不要在这里抛异常。
    注意 GetParent 这一层：Tk 每个部件都有自己的 HWND，真正那个
    带边框的顶层窗口在父级上，Class 名叫 TkTopLevel。
    """
    try:
        import ctypes
        hid = widget.winfo_id()
        return ctypes.windll.user32.GetParent(hid) or hid
    except Exception:                 # noqa: BLE001
        return 0


def move_window(widget, x, y):
    """把顶层窗口移到绝对坐标 (x, y)，允许负值。返回是否成功。"""
    hwnd = hwnd_of(widget)
    if not hwnd:
        return False
    try:
        import ctypes
        # SWP_NOSIZE | SWP_NOZORDER | SWP_NOACTIVATE
        return bool(ctypes.windll.user32.SetWindowPos(
            hwnd, 0, int(x), int(y), 0, 0, 0x0001 | 0x0004 | 0x0010))
    except Exception:                 # noqa: BLE001
        return False


def set_window_pos(widget, x, y):
    """
    摆放顶层窗口的位置。这是全程序**唯一**该写窗口位置的地方。

    为什么要分两条路 —— Tk 的 geometry 字符串里，负号不是负号：
        "+80-292" 的含义是「距屏幕右边? 不，距屏幕**底边** 292」，
        而不是「y 坐标等于 -292」。
    所以窗口坐标一旦为负，用 geometry 表达出来的位置就是错的：
      · 多显示器把扩展屏摆在主屏左边/上边时，虚拟桌面起点就是负的；
      · 小屏笔记本上面板比屏幕还高，要往上挪时，y 也会变负。
    这两种情况都只能直接调系统接口，走 SetWindowPos。
    坐标非负时仍然走 Tk 老路子，保持和以前完全一致的行为。
    """
    x, y = int(x), int(y)
    if x >= 0 and y >= 0:
        widget.geometry("+%d+%d" % (x, y))
        return
    if not move_window(widget, x, y):
        # 系统接口都失败了就只能认了：负坐标喂给 geometry 不报错也不生效，
        # 窗口留在原地，总好过挪到错误的位置上去。
        pass


def set_geometry(widget, w, h, x, y):
    """同时定尺寸和位置（位置允许为负，见 set_window_pos）。"""
    widget.geometry("%dx%d" % (int(w), int(h)))
    set_window_pos(widget, x, y)


def chrome_hidden(win):
    """
    这个窗口现在是不是「自绘无边框」——即系统标题栏已经被取消。

    为什么不用 win.overrideredirect() 直接查：tkinter 那层封装把 Tcl 返回的
    "0" 读成了 None，于是「边框已交还给系统」时拿到的是 None 而不是 False，
    写 `is False` 的断言永远不成立 —— 测试会报一个看不出原因的假失败
    （2026-09-19 最小化功能自检就这样卡了一轮）。直接问 Tcl 得到的是干净的
    "1"/"0"，不存在这个歧义。
    """
    try:
        return str(win.tk.call("wm", "overrideredirect", win._w)).strip() in ("1", "true", "True")
    except Exception:
        return False


def acquire_single_instance():
    """
    单实例锁。True = 本进程是唯一实例；False = 已经有实例在跑了。

    用系统命名互斥体而不是锁文件：进程被强杀（任务管理器结束进程）时，
    系统会自动释放，不会留下一个假的「已经在运行」状态把程序永久锁死。

    锁名带上数据目录的指纹：正常使用时所有实例共用同一个目录，行为不变；
    演练（设了 ANCIENT_COUNTDOWN_HOME）则另开一把锁，不会把真程序挡在门外。
    """
    try:
        import ctypes
        # use_last_error=True：否则 CreateMutexW 之后读到的 last error
        # 可能已经被解释器内部的其它调用覆盖掉
        k32 = ctypes.WinDLL("kernel32", use_last_error=True)
        tag = hashlib.md5(os.path.abspath(DATA_DIR).lower().encode("utf-8")).hexdigest()[:12]
        handle = k32.CreateMutexW(None, False, "%s_%s" % (MUTEX_NAME, tag))
        if not handle:
            return True                      # 系统调用失败就放行，不要反过来卡住自己
        if ctypes.get_last_error() == 183:   # ERROR_ALREADY_EXISTS
            return False
        return True                          # handle 故意不关闭，锁随进程存活
    except Exception:
        return True


def request_wake():
    """请已有实例把窗口挪到可见处——用户双击，本意就是「我要看见它」。"""
    ok, _ = reg_store_write("wake", {"pid": os.getpid()})
    return ok


def clear_wake_file():
    """清掉可能残留的唤醒信号，避免刚启动就自己触发一次「现身」。"""
    reg_store_delete("wake")


def script_home():
    """
    程序自己所在的目录（每次都现算，不缓存）。

    单独抽出来是因为 app_dir() 的结果会被 DATA_DIR 拿去当常量存下来，
    而「把发信脚本放哪儿」这件事是随时要问的 —— 两件事混用一个入口，
    测试里想模拟 exe 环境就得连模块一起重载，太重了。
    """
    if getattr(sys, "frozen", False):
        return os.path.dirname(os.path.abspath(sys.executable))
    try:
        return os.path.dirname(os.path.abspath(__file__))
    except NameError:
        return os.path.dirname(os.path.abspath(sys.argv[0]))


def app_dir():
    """程序所在目录（兼容 PyInstaller 打包后的 exe）。"""
    return script_home()


def data_dir():
    """
    配置与状态文件的存放目录。

    默认就是程序所在目录，和以前完全一样。
    只有设了环境变量 ANCIENT_COUNTDOWN_HOME 时才改道 —— 这个口子留给
    「演练」用：自检、试跑、测量时把数据写进临时目录，
    就不会把使用者真正的配置和寄信履历弄脏。
    """
    override = os.environ.get("ANCIENT_COUNTDOWN_HOME")
    if override:
        try:
            os.makedirs(override, exist_ok=True)
            return override
        except OSError:
            pass
    return app_dir()


DATA_DIR = data_dir()

CONFIG_PATH = os.path.join(DATA_DIR, "countdown_config.json")
NOTIFY_TASK_PATH = os.path.join(DATA_DIR, NOTIFY_TASK_FILE)
NOTIFY_RESULT_PATH = os.path.join(DATA_DIR, NOTIFY_RESULT_FILE)
NOTIFY_TEST_RESULT_PATH = os.path.join(DATA_DIR, NOTIFY_TEST_RESULT_FILE)
NOTIFY_STATE_PATH = os.path.join(DATA_DIR, NOTIFY_STATE_FILE)
NOTIFY_SECRET_PATH = os.path.join(DATA_DIR, NOTIFY_SECRET_FILE)
# 发信脚本是「程序」不是「数据」，始终跟着程序走
MAILER_PATH = os.path.join(app_dir(), MAILER_FILE)


# --------------------------------------------------------------------------
# 数据仓 · 注册表
#
# 配置、凭据、履历全部存进注册表（HKCU\Software\AncientCountdown），
# 程序目录里不再出现任何数据文件 —— 文件夹里永远只有程序本身。
#
# 为什么不是「把配置写进 exe 里」：exe 运行时是只读的，程序不能修改自己，
# 而这些数据恰恰是随时要写的（窗口位置、目标时刻、寄信履历）。
# 注册表是 Windows 给「程序要写、又不该满地留文件」准备的正经地方，
# 微信/QQ 的本地设置也存在这里。
#
# 演练隔离：设了 ANCIENT_COUNTDOWN_HOME 时，读写改道到 Software\AncientCountdown_Test，
# 真实数据分毫不动 —— 和旧版「改道到临时目录」一个思路，只是阵地从文件换成了注册表。
# --------------------------------------------------------------------------

REG_STORE_ROOT = r"Software\AncientCountdown"


def reg_store_key():
    """当前进程该用哪个注册表键。演练时带 _Test 后缀，绝不碰真实数据。"""
    if os.environ.get("ANCIENT_COUNTDOWN_HOME"):
        return REG_STORE_ROOT + "_Test"
    return REG_STORE_ROOT


def reg_store_read(name, fallback):
    """读一个 JSON 值。键不存在或内容损坏时返回 fallback 的深拷贝。"""
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, reg_store_key(), 0,
                            winreg.KEY_READ) as key:
            raw, _ = winreg.QueryValueEx(key, name)
        data = json.loads(raw)
    except (OSError, ValueError):
        return json.loads(json.dumps(fallback))
    if data is None:
        return json.loads(json.dumps(fallback))
    return data


def reg_store_write(name, data):
    """写一个 JSON 值。注册表单值上限约 1MB，本程序所有数据远小于此。"""
    try:
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, reg_store_key()) as key:
            winreg.SetValueEx(key, name, 0, winreg.REG_SZ,
                              json.dumps(data, ensure_ascii=False))
        return True, ""
    except OSError as exc:
        return False, str(exc)


def reg_store_delete(name):
    """删一个值。不存在也当删成功（幂等）。"""
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, reg_store_key(), 0,
                            winreg.KEY_SET_VALUE) as key:
            winreg.DeleteValue(key, name)
    except OSError:
        pass


def reg_store_drop_all(key_path):
    """整个删掉一个数据键（恢复出厂与演练收尾用）。本程序的键没有子键。"""
    try:
        winreg.DeleteKey(winreg.HKEY_CURRENT_USER, key_path)
    except OSError:
        pass


def migrate_legacy_files():
    """
    老版本把配置/凭据/履历放在程序旁边的文件里；升级后搬进注册表。

    只在真实模式跑一次（演练目录里不会有旧文件）。搬完把旧文件删干净 ——
    包括可能残留的瞬态文件（任务/结果/唤醒信号，任务里含授权码，绝不过夜）。
    任何一步失败都保留原文件，下次启动再试；数据以文件为准（只有旧版本写过它）。
    """
    if os.environ.get("ANCIENT_COUNTDOWN_HOME"):
        return
    pairs = [(CONFIG_PATH, "config"),
             (NOTIFY_SECRET_PATH, "notify_secret"),
             (NOTIFY_STATE_PATH, "notify_state")]
    for path, name in pairs:
        try:
            with open(path, "r", encoding="utf-8") as fp:
                data = json.load(fp)
        except Exception:                         # noqa: BLE001
            continue                              # 文件不存在或损坏 —— 没有可搬的
        ok, _ = reg_store_write(name, data)
        if not ok:
            continue                              # 写注册表失败：保留文件下次再试
        try:
            os.remove(path)
        except OSError:
            pass
    # 瞬态残留：任务（含授权码）/结果/唤醒信号，连同可能的 .tmp 半截文件
    for junk in (NOTIFY_TASK_PATH, NOTIFY_RESULT_PATH, NOTIFY_TEST_RESULT_PATH,
                 os.path.join(DATA_DIR, WAKE_FILE)):
        for p in (junk, junk + ".tmp"):
            try:
                os.remove(p)
            except OSError:
                pass


def deep_merge(base, override):
    """把 override 合并进 base 的副本（保留 base 中缺失的默认键）。"""
    out = dict(base)
    for k, v in (override or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def load_config():
    try:
        raw = reg_store_read("config", {})
        if not isinstance(raw, dict):
            raw = {}
    except Exception:
        # 首次运行读不到、或配置损坏 —— 都当空配置处理，不阻塞启动
        raw = {}

    # 先深拷贝默认值：deep_merge 只做浅拷贝，仓里缺哪个键，
    # 合并结果里那一层就和模块级 DEFAULT_CONFIG 共用同一个 dict，
    # 后面任何就地改动（比如给 notify 补种抬头）都会把默认值本身弄脏。
    base = json.loads(json.dumps(DEFAULT_CONFIG))
    cfg = deep_merge(base, raw)

    # 一次性补种本机抬头：仓里没有这个键时，用计算机名种进去，
    # 这样多台机器装上去开箱就能分辨，用户想改成「书房台机」再改。
    # 判据必须是「原始配置有没有这个键」，不能看合并后的值 ——
    # 合并会把默认值补上，就分不清「从没设过」和「用户特意清空了」。
    if "signature" not in (raw.get("notify") or {}):
        cfg["notify"] = dict(cfg.get("notify") or {}, signature=machine_name())
    return cfg


def save_config(cfg):
    return reg_store_write("config", cfg)


def reset_factory_data():
    """
    恢复出厂设置的「数据部分」：整个删掉数据键，再按空仓重新读出三份默认数据。

    为什么要单独拆出一个不带界面的函数：
      · 只删注册表是假干净 —— 内存里还抱着旧配置，下一次 tick 记窗口位置、
        或者退出时落盘，都会把旧配置原样写回去，删掉的键转眼复活，用户点了白点。
        所以删完必须立刻重新加载，让内存也回到初始值。
      · 分开之后，自检脚本可以只测数据这一段（不用开窗口就能断言），
        界面刷新那部分留给 CountdownApp.factory_reset 单独负责。

    删完刻意不回写：空仓才是「从没配置过」的真实状态，
    配置会在用户下一次真的改动时自然落盘（那时写的已经是默认值了）。

    返回 (cfg, secret, notify_state) 三份全新的默认数据。
    notify.signature 由 load_config 按「首次运行」的规则补种本机名，
    和刚装好时一模一样。
    """
    reg_store_drop_all(reg_store_key())
    return load_config(), load_notify_secret(), load_notify_state()


# --------------------------------------------------------------------------
# 共用设置 · 多台机器同步同一份配置
#
# 一份文件搬来搬去，规矩只有三条：
#   ① 文件放 exe 旁边，启动时读进去（读到就吃，吃完就删）
#   ② 本机抬头与开机自启**永不**被这份文件改掉 —— 它们天生各机不同
#   ③ 文件里带着邮箱授权码（明文），所以它和密钥同级看待，绝不入库
#
# 为什么不做成「常驻的配置文件」而是「读一次就销毁」：
# 常驻的话，用户在界面上改的设置下一次启动就被文件盖回去，会显得
# 「改了不生效」；而且程序目录里会永远多出一个文件。读一次吃一次，
# 文件只承担「投喂」这一个角色，两边都不别扭。
# --------------------------------------------------------------------------

SHARED_NOTE = (
    "这份文件是「古风倒计时」的跨机器设置，由设置面板的「导出共用设置」生成。\n"
    "拷到另一台机器上之后，在那台机器的设置面板里点「从文件导入…」选中它，\n"
    "设置当场生效。程序不会自己去找这个文件、也不会删它 —— 什么时候导入、\n"
    "导哪一份，都由你当场决定。\n"
    "· 导出时可以一项一项挑，下面「include」写的就是这一份带了哪些项；\n"
    "  没带的那些，对方机器上原来的设置会原样保留，不会被这里覆盖。\n"
    "· 本机抬头（寄信署名）不在这个文件里，每台机器各自设。\n"
    "· 开机自启也不在里面，那是每台机器自己的事。\n"
    "· 文件里可能有邮箱授权码，是明文。别放进公共网盘、别发到群里。\n"
    "· 想改内容就用记事本改（存成 UTF-8），再拷给别的机器。改坏了程序会\n"
    "  拒绝读入，并且故意不删文件，方便你改回来。"
)


# 导出时可以一项一项挑 —— 见 build_shared_bundle 的 selection 参数。
#
# 为什么要能挑：用户手上是一批机器，绝大多数设置想配成一样，可「目标时刻」
# 偏偏是每台各不相同的（每台在倒计自己的事）。不挑的话，一次同步就把所有
# 机器的时刻冲成同一个 —— 那正是最不能出的事。
#
# 语义是「剔除」而不是「只留」：没勾的项从包里删掉，没在这张表里的键照常
# 带着走。这样以后新增了配置项，也会自动跟着同步，不会静默漏掉。
SHARED_ITEMS = (
    {"key": "target", "label": "目标时刻", "default": False,
     "hint": "每台机器倒计的事多半不一样，默认不带",
     "drop": (("config", "target"),)},
    {"key": "thresholds", "label": "颜色规则", "default": True,
     "hint": "剩几天时换成什么颜色",
     "drop": (("config", "thresholds"),)},
    {"key": "palette", "label": "配色", "default": True,
     "hint": "宣纸底色、墨色、朱砂这一整套颜色",
     "drop": (("config", "palette"),)},
    {"key": "zero", "label": "归零时的文字与颜色", "default": True,
     "hint": "「時辰已到」这行字和它闪的颜色",
     "drop": (("config", "zero_text"), ("config", "zero_color"),
              ("config", "zero_color_alt"))},
    {"key": "notify", "label": "鸿雁传书设置", "default": True,
     "hint": "服务商、发件与收件邮箱、提醒档位（本机抬头不带）",
     "drop": (("config", "notify"),)},
    {"key": "secret", "label": "邮箱授权码", "default": True,
     "hint": "明文写进文件里：别放公共网盘、别发到群里",
     "drop": (("notify_secret",),)},
    {"key": "pins", "label": "锁定与置顶", "default": True,
     "hint": "是否锁定尺寸、是否总在最前",
     "drop": (("config", "locked"), ("config", "always_on_top"))},
    {"key": "window", "label": "窗口位置与大小", "default": True,
     "hint": "各机器屏幕不一样的话可以不带",
     "drop": (("config", "window"),)},
    {"key": "autoupdate", "label": "自动检查更新", "default": True,
     "hint": "是否开机后自己去找新版本",
     "drop": (("config", "auto_update_check"),)},
)

# 上次导出勾了哪几项，也记在注册表里（不是用户设置，只是个记忆）
SHARED_ITEMS_KEY = "shared_export_items"


def shared_item_keys():
    """所有可选项的 key，按界面上的显示顺序。"""
    return [it["key"] for it in SHARED_ITEMS]


def default_shared_selection():
    """默认勾哪些：除「目标时刻」外全勾。"""
    return dict((it["key"], bool(it["default"])) for it in SHARED_ITEMS)


def load_shared_selection():
    """
    上次导出时勾了哪几项；从没导过就用默认值（缺的项按默认补上）。

    记住它有实际意义：一次要给十来台机器配，每次都重新勾一遍很烦，
    而每次要的又几乎总是同一套。
    """
    sel = default_shared_selection()
    saved = reg_store_read(SHARED_ITEMS_KEY, {})
    if isinstance(saved, dict):
        for key in sel:
            if key in saved:
                sel[key] = bool(saved[key])
    return sel


def save_shared_selection(sel):
    """把勾选结果记下来，下次打开导出窗口时还是这一套。"""
    if isinstance(sel, dict):
        reg_store_write(SHARED_ITEMS_KEY,
                        dict((k, bool(v)) for k, v in sel.items()))


def _drop_shared_path(bundle, path):
    """按路径从包里删掉一项；路径上哪一层不存在就安静地什么都不做。"""
    node = bundle
    for name in path[:-1]:
        if not isinstance(node, dict) or name not in node:
            return
        node = node[name]
    if isinstance(node, dict):
        node.pop(path[-1], None)


def shared_file_path():
    """共用设置文件在哪儿：程序（数据）目录下。演练时跟着改道走。"""
    return os.path.join(DATA_DIR, SHARED_FILE)


def build_shared_bundle(cfg, secret, selection=None):
    """
    攒出「可以搬去别的机器」的那部分设置。

    selection 是导出界面上勾的项目（形如 {"target": False, ...}）：
      · 传 None = 全带（老代码与测试走这条路）
      · 传了就按勾选项剔除 —— 没勾的项根本不进文件，
        也就不可能覆盖对方机器上那一项。

    搬什么、不搬什么，是这段逻辑最要紧的地方：

      搬：目标时刻、颜色规则、配色、传书设置（服务商/账号/收件人/档位）、
          锁定与置顶、窗口大小与位置（具体带哪几项由 selection 定）。
      不搬 notify.signature（本机抬头）—— 各台机器刻意不同，搬过去会把
          对方的抬头冲掉，而抬头恰恰是用户唯一想区分开的东西。
      不搬 autostart —— 它背后是注册表 Run 键里一条带着 exe 完整路径的命令，
          各机不同；更要紧的是：把 A 机的「关」搬给 B 机，等于偷偷关掉 B 机
          的自启，用户只会看到「倒计时怎么不自己出来了」。
      不搬 notify_state（寄信履历）—— 那是运行痕迹不是设置。搬过去会让新机器
          以为「这几档已经寄过了」，真正的提醒反而不寄了。
    """
    snap = json.loads(json.dumps(cfg or {}))       # 深拷贝，绝不改调用方的对象
    snap.pop("autostart", None)
    nd = snap.get("notify")
    if isinstance(nd, dict):
        nd.pop("signature", None)
    sec = secret if isinstance(secret, dict) else {}
    bundle = {
        "_说明": SHARED_NOTE,
        "schema": SHARED_SCHEMA,
        "app": APP_NAME,
        "version": APP_VERSION,
        "exported_at": _stamp(),
        "config": snap,
        "notify_secret": {"smtp_password": sec.get("smtp_password") or ""},
    }
    if selection is not None:
        picked = set(k for k in shared_item_keys() if selection.get(k))
        for spec in SHARED_ITEMS:
            if spec["key"] in picked:
                continue
            for path in spec["drop"]:
                _drop_shared_path(bundle, path)
        # 写进文件里：用户拿记事本打开时能一眼看出「这份带了什么」，
        # 不至于把只带颜色的那份当成全量，拷给机器才发现时刻没跟着走。
        bundle["include"] = [it["label"] for it in SHARED_ITEMS
                             if it["key"] in picked]
    return bundle


def parse_shared_bundle(blob):
    """
    把文件内容读成设置包。返回 (包, None) 或 (None, 失败原因)。

    两种写法都认：
      ① 完整形态（导出时写的）：{"config": {...}, "notify_secret": {...}}
      ② 裸配置：整份就是配置本身 —— 有人会把老版本留下的
         countdown_config.json 直接改名拿过来用，不该让他白跑一趟。
    """
    try:
        data = json.loads(blob.decode("utf-8-sig"))
    except UnicodeDecodeError:
        return None, ("这个文件不是 UTF-8 文本，程序读不了。"
                      "请用记事本打开、另存为时把编码选成 UTF-8。")
    except ValueError as exc:
        return None, "这个文件不是合法的设置文件（%s）" % exc
    if not isinstance(data, dict):
        return None, "这个文件的内容不是一个设置对象"
    if isinstance(data.get("config"), dict):
        return data, None
    return {"config": data}, None


def apply_shared_config(bundle):
    """
    把一份设置包写进注册表 —— 合并，文件里有的键一律以文件为准。

    返回 (是否写入, 失败原因)。
    """
    if not isinstance(bundle, dict):
        return False, "内容不是一个设置对象"
    cfg_in = bundle.get("config")
    if not isinstance(cfg_in, dict):
        return False, "里面没有 config 这一段"

    cfg_in = json.loads(json.dumps(cfg_in))
    # 双保险：导出时不写抬头和自启，导入时也不认 —— 就算有人手工往文件里
    # 加了这两项，也顶不掉本机的抬头、也不会关掉本机的自启。
    cfg_in.pop("autostart", None)
    nd = cfg_in.get("notify")
    if isinstance(nd, dict):
        nd.pop("signature", None)

    cur = reg_store_read("config", {})
    if not isinstance(cur, dict):
        cur = {}
    # deep_merge 只覆盖 files 里出现的键，所以本机抬头（不在文件里）原样留着。
    # 本机从没设过抬头时这里也没有 signature，交给 load_config 按「首次运行」
    # 补种计算机名 —— 正是多机同步想要的效果：设置一样，抬头各不相同。
    merged = deep_merge(cur, cfg_in)
    ok, err = reg_store_write("config", merged)
    if not ok:
        return False, "设置写不进注册表：%s" % err

    sec_in = bundle.get("notify_secret")
    if isinstance(sec_in, dict) and (sec_in.get("smtp_password") or "").strip():
        cur_sec = reg_store_read("notify_secret", {"smtp_password": ""})
        if not isinstance(cur_sec, dict):
            cur_sec = {"smtp_password": ""}
        cur_sec["smtp_password"] = sec_in["smtp_password"]
        ok2, err2 = reg_store_write("notify_secret", cur_sec)
        if not ok2:
            return False, "授权码写不进注册表：%s" % err2
    return True, ""


def export_shared_config(path, cfg, secret, selection=None):
    """
    把当前设置写成一份共用设置文件。返回 (True, None) 或 (False, 失败原因)。

    selection 见 build_shared_bundle；None = 全带。
    """
    bundle = build_shared_bundle(cfg, secret, selection)
    text = json.dumps(bundle, ensure_ascii=False, indent=2) + "\n"
    try:
        # 带 BOM 写：用户多半会拿记事本打开看一眼，老记事本见到没 BOM 的
        # UTF-8 会认成 ANSI，中文全糊。读回来时 utf-8-sig 会把 BOM 吃掉，对得上。
        with open(path, "w", encoding="utf-8-sig", newline="\n") as fh:
            fh.write(text)
        return True, None
    except OSError as exc:
        return False, "%s" % exc


def _note_shared_result(status, note):
    """把最近一次共用设置的导入结果记下来，供设置面板显示（失败才另记一条）。"""
    reg_store_write(SHARED_LAST_KEY, {"at": _stamp(), "status": status,
                                      "note": note})
    if status == "bad":
        reg_store_write(SHARED_ERR_KEY, {"at": _stamp(), "note": note})


def shared_last_result():
    """最近一次导入的结果；从没导入过就返回空 dict。"""
    data = reg_store_read(SHARED_LAST_KEY, {})
    return data if isinstance(data, dict) else {}


def apply_shared_file(path):
    """
    从指定的文件导入设置 —— 导入只有这一条路：设置面板里的「从文件导入…」。

    曾经做过「启动时扫 exe 旁边、有就读走」，v1.6 起去掉了，原因见本文件
    顶部共用设置那段说明：自动覆盖会把这台机器上独有的设置冲掉，而且出事时
    用户根本不知道是文件干的。改成手动挑文件之后，什么时候导入、导哪一份，
    都是用户当场看见、当场决定的。

    **不删文件**：用户主动挑进来的那份很可能就是他留着的母本，替他删掉是添乱。
    返回 (状态, 说明)。
    """
    try:
        with open(path, "rb") as fh:
            blob = fh.read()
    except OSError as exc:
        return "bad", "读不到这个文件：%s" % exc
    bundle, err = parse_shared_bundle(blob)
    if bundle is None:
        _note_shared_result("bad", err)
        return "bad", err
    ok, err = apply_shared_config(bundle)
    if not ok:
        _note_shared_result("bad", err)
        return "bad", err
    _note_shared_result("applied", "已导入")
    return "applied", "已导入"


# --------------------------------------------------------------------------
# 鸿雁传书 · 状态与凭据
#
# 三份数据各司其职，互不干扰（都在注册表键里，值名区分）：
#   config          你的设置（可随意分享）
#   notify_secret   邮箱授权码（含密码，别外传）
#   notify_state    发送履历（程序自己维护，你不需要看）
# 拆开的好处是：频繁写履历不会碰到设置数据，也就不会把设置写坏。
# --------------------------------------------------------------------------

def _stamp(fmt="%Y-%m-%d %H:%M:%S"):
    return datetime.datetime.now().strftime(fmt)


def load_notify_state():
    st = reg_store_read("notify_state", {"target_key": "", "history": []})
    if not isinstance(st, dict):
        st = {"target_key": "", "history": []}
    st.setdefault("target_key", "")
    if not isinstance(st.get("history"), list):
        st["history"] = []
    return st


def save_notify_state(st):
    return reg_store_write("notify_state", st)


def load_notify_secret():
    sec = reg_store_read("notify_secret", {"smtp_password": ""})
    if not isinstance(sec, dict):
        sec = {"smtp_password": ""}
    sec.setdefault("smtp_password", "")
    return sec


def save_notify_secret(sec):
    return reg_store_write("notify_secret", sec)


def is_frozen():
    """是不是被打包成了 exe。"""
    return bool(getattr(sys, "frozen", False))


def looks_like_python(exe):
    """这个路径像个 Python 解释器（含 python3.14.exe / pythonw.exe 这类带版本号的）。"""
    base = os.path.basename(exe or "").lower()
    return base.startswith("python") or base.startswith("py")


def resolve_python():
    """
    找一个能跑 .pyw 的解释器 —— 发信脚本要靠它启动。

    平时开发运行（python AncientCountdown.pyw），sys.executable 就是解释器本身。
    打包成 exe 之后 sys.executable 变成 exe，已经不是解释器了，
    得去 PATH 和各处常见位置摸一遍；摸不到就回退到自带的 python 启动器 py.exe。
    """
    exe = sys.executable or ""
    if exe and not is_frozen() and looks_like_python(exe):
        if exe.lower().endswith("python.exe"):
            cand = exe[:-len("python.exe")] + "pythonw.exe"
            if os.path.exists(cand):
                return cand
        return exe

    which = shutil.which("pythonw") or shutil.which("python")
    if which:
        return which
    # (c) 实在找不到就退回系统的 py 启动器 —— 它按 shebang / 注册表找解释器
    return which or "py"


def ensure_mailer():
    """
    找出发信脚本在哪，返回路径；找不到返回 None。**只找，不落盘。**

    源码模式：脚本就在程序旁边，直接返回。
    打包成单个 exe：脚本被打进 exe 里（见 打包.py 的 --add-data），运行时
    可以按 _MEIPASS 找到；这个路径只在本次进程存活期间有效，而发信进程
    是「exe 自己兼任发信脚本」（见 mailer_target），它启动时会再解一份自己的，
    所以这里不必、也不该把脚本复制出来。

    2026-09-19 改：**取消了「程序旁边没有就照存一份」的旧行为**。
    那个行为本意是让用户能翻到脚本自己核对内容，但代价是每寄一次信
    （含点一次「试寄一封」）就往 exe 同目录丢一个 mailer.pyw ——
    而用户明确要求「程序目录里永远只有 exe 一个文件」。
    想核对脚本内容的话，发布包里本来就有一份。

    注意这里用的是「存脚本的那个目录」而不是 app_dir()：
    app_dir() 是模块加载时算好的常量（DATA_DIR 也一样），
    测试要让它变就得连整个模块重载 —— 那是测试在给代码让路。
    抽成函数之后，跑一次就是读一次，没有可缓存的状态。
    """
    here = os.path.join(script_home(), MAILER_FILE)
    if os.path.exists(here):
        return here
    if is_frozen():
        src = os.path.join(getattr(sys, "_MEIPASS", "") or "", MAILER_FILE)
        if os.path.exists(src):
            return src
    return None


def mailer_target():
    """
    交给发信进程的执行目标。
    正常是 .pyw 脚本路径；打包后就让 exe 自己兼任发信脚本（argv 只给 "mailer"）。

    踩过的坑：打包版曾把 mailer.pyw 的完整路径塞进 argv —— 而主程序 main()
    的判据是 argv[1] == "mailer"，完整路径对不上号，子进程就走了正常 GUI
    启动：撞上单实例锁 → 给主实例留「现身」信号 → 主窗口被拉回默认位置。
    用户看到的是「点一下试寄，倒计时自己挪位了，信也没影」。改成只传
    "mailer" 后，spawn 形态、main() 判据、run_mailer_cli 的过滤、打包冒烟
    四处终于说的是同一种话。脚本路径本身不用传：run_mailer_cli 会去
    _MEIPASS（exe 内嵌副本）找 mailer.pyw，找不到再退回 exe 旁边那份。
    """
    path = ensure_mailer()
    if not path:
        return path, []
    if is_frozen() and os.path.basename(sys.executable).lower().endswith(".exe"):
        return sys.executable, ["mailer"]
    return path, []


def run_mailer_cli(argv):
    """
    `AncientCountdown.exe mailer ...` —— 让打包后的 exe 反过来当发信脚本用。

    单文件 exe 每次启动都要把自己解包一遍，发一封信多花一两秒，
    换来的是「不依赖用户机器上装没装 Python」。这是打包后唯一的可靠路径。

    踩过的坑：窗口模式（--windowed）的 exe 没有真正的控制台，
    stdout / stderr 是无效句柄 —— 而 mailer 里任何一句输出或异常回溯
    都会去写它，**一写就卡死**（实测进程挂着不退、任务文件也没被处理）。
    所以这里先把三个标准流换成「黑洞」，再让脚本跑。
    """
    import runpy

    class _Sink(object):
        """能接住任何写入、且永远不报错的假流。"""

        def write(self, *_a):
            return 0

        def writelines(self, *_a):
            return None

        def flush(self):
            return None

        def isatty(self):
            return False

        def fileno(self):
            raise OSError("no fileno")

    for name in ("stdout", "stderr", "stdin"):
        try:
            setattr(sys, name, _Sink() if name != "stdin" else _Sink())
        except Exception:               # noqa: BLE001
            pass

    # 把 mailer 要用的模块在这里先导入一遍。
    #
    # 打包后 mailer.pyw 是「数据」，PyInstaller 静态分析看不到它的 import，
    # 于是 exe 里可能缺 smtplib / email 这些模块 —— 一跑就 ModuleNotFoundError。
    # 打包脚本里也有一份 --hidden-import 名单，两边都写是有意的：
    # 名单写漏了，这里还能兜住；这里被删了，名单还能兜住。
    # 发信是低频动作，先付一次导入成本，比「信寄不出去」划算太多。
    try:
        import smtplib      # noqa: F401
        import ssl          # noqa: F401
        import email        # noqa: F401
        import email.message    # noqa: F401
        import email.utils      # noqa: F401
        import email.mime.text  # noqa: F401
    except Exception:                   # noqa: BLE001
        pass

    args = [a for a in argv if a != "mailer"]
    src = os.path.join(getattr(sys, "_MEIPASS", "") or "", MAILER_FILE)
    if not os.path.exists(src):
        src = os.path.join(script_home(), MAILER_FILE)
    if not os.path.exists(src):
        _mailer_error_log("找不到发信脚本：\n  _MEIPASS = %r\n  script_home() = %r\n  试过 = %r"
                          % (getattr(sys, "_MEIPASS", None), script_home(),
                             os.path.join(getattr(sys, "_MEIPASS", "") or "", MAILER_FILE)))
        return 2
    # 告诉 mailer 去哪儿读写任务与结果文件。
    #
    # 这一句是打包后最容易出错的地方：mailer.pyw 是脚本不是数据，
    # 它读的是环境变量，拿不到就会退回到「自己所在的目录」——
    # 而 exe 模式下它所在的目录是 _MEIPASS（那个用完就删的解包临时目录），
    # 任务文件根本不在那儿，结果就是「发了信但永远没结果」。
    # 主程序调用时本来就会带上这个变量（见 _spawn_mailer），
    # 这里是给「手工敲 exe mailer」留的兜底。
    if not os.environ.get("ANCIENT_COUNTDOWN_HOME"):
        os.environ["ANCIENT_COUNTDOWN_HOME"] = script_home()
    sys.argv = [src] + args
    try:
        runpy.run_path(src, run_name="__main__")
        return 0
    except SystemExit as exc:
        # mailer 用 sys.exit(0/1/2) 汇报结果，正常路径
        return int(exc.code or 0)
    except BaseException:               # noqa: BLE001
        # 窗口模式没有控制台，异常打出去也没人看得见 —— 落一份日志到旁边
        import traceback
        _mailer_error_log(traceback.format_exc())
        return 1


def _mailer_error_log(text):
    """
    发信进程出岔子时的落盘日志。

    打包后的程序没有控制台，发信又是派生的隐藏进程 —— 一旦出错，
    用户看到的现象只是「信没来」，没有任何线索。留一份日志，
    排查时至少有东西可看。日志只保留最近一次，不会无限长大。

    落在 %TEMP% 而不是程序旁边：程序目录要保持「只有 exe 一个文件」，
    这份日志又只在出错时才有内容，放临时目录既不影响排查，
    也不会在用户眼皮底下多出一个说不清的文件。
    （崩溃日志 ac_crash.log 早就是这么做的，见 install_crash_hook。）
    """
    try:
        import tempfile
        path = os.path.join(tempfile.gettempdir(), "ac_mailer_error.txt")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("时间: %s\n\n%s\n" % (_stamp(), text))
    except Exception:                   # noqa: BLE001
        pass


def pythonw_executable():
    """
    找不带控制台窗口的解释器。

    用户从命令行启动时 sys.executable 可能是 python.exe，直接派生子进程
    会闪出一个黑框。这里换成旁边的 pythonw.exe。
    """
    return resolve_python()


def autostart_command():
    """
    开机时要执行的命令行。

    打包版：exe 自己就能跑，引号包住防路径空格。
    源码版：用 pythonw.exe 带上脚本全路径 —— 开机没有控制台可闪，
    必须用无窗解释器，否则每次开机都蹦一个黑框。
    """
    if is_frozen():
        return '"%s"' % sys.executable
    script = globals().get("__file__") or sys.argv[0]
    return '"%s" "%s"' % (pythonw_executable(), os.path.abspath(script))


def is_autostart_on():
    """
    注册表里现在到底挂没挂启动项。

    勾选框的初值以这里的答案为准，而不是配置文件：万一启动项被
    安全软件或用户手动清掉了，面板上再显示「已勾选」就是在撒谎。
    """
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_PATH, 0,
                            winreg.KEY_READ) as key:
            winreg.QueryValueEx(key, AUTOSTART_VALUE_NAME)
        return True
    except OSError:                     # noqa: B014 - 键或值任一不存在都算「没开」
        return False


def set_autostart(enabled):
    """
    开 / 关开机自动运行。

    关：只删我们自己的那一个值，别的程序的自启项一律不碰；
    值或键本来就不存在也算关成功（幂等，勾了又取消不会报错）。
    返回 True 表示注册表已同步；极少见的权限失败返回 False，
    此时勾选框下次打开仍会按注册表实况显示，不会留下假状态。
    """
    try:
        if not enabled:
            try:
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_PATH,
                                    0, winreg.KEY_SET_VALUE) as key:
                    winreg.DeleteValue(key, AUTOSTART_VALUE_NAME)
            except FileNotFoundError:
                pass                    # 本来就没挂，目的已达成
        else:
            cmd = autostart_command()
            try:
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_PATH,
                                    0, winreg.KEY_SET_VALUE) as key:
                    winreg.SetValueEx(key, AUTOSTART_VALUE_NAME, 0,
                                      winreg.REG_SZ, cmd)
            except FileNotFoundError:
                # Run 键被整个删掉过（个别优化软件干得出来），现建一个
                with winreg.CreateKey(winreg.HKEY_CURRENT_USER,
                                      AUTOSTART_RUN_PATH) as key:
                    winreg.SetValueEx(key, AUTOSTART_VALUE_NAME, 0,
                                      winreg.REG_SZ, cmd)
        return True
    except OSError:
        return False


def _rule_label(days):
    """通知规则的默认档位名。"""
    try:
        days = float(days)
    except (TypeError, ValueError):
        return "提醒"
    if days <= 0:
        return "时辰已到"
    if days >= 1:
        return "剩 %g 日" % days
    hours = days * 24
    if abs(hours - round(hours)) < 0.02:
        return "剩 %d 时" % round(hours)
    return "剩 %.1f 时" % hours


def looks_like_mail(addr):
    """
    粗校验邮箱地址的形状。

    只做「一眼能看出错」的判断，不追求符合 RFC —— 真伪最终由邮件服务器裁定。
    但少写一个点这种最常见的手误必须在这里拦下：放过去的话，
    QQ 会直接把连接掐断，使用者看到的是一句英文，根本联想不到是自己打错了。

    注意：mailer.pyw 里有同名同逻辑的一份。发信脚本要能独立运行，
    不能反过来 import 主程序，所以这份重复是有意留的，改一处要记得改两处。
    """
    addr = (addr or "").strip()
    if not addr or " " in addr or addr.count("@") != 1:
        return False
    local, _, domain = addr.partition("@")
    if not local or not domain:
        return False
    if "." not in domain or domain.startswith(".") or domain.endswith("."):
        return False
    return True


def machine_name():
    """
    本机名 —— 用来在收件箱里分辨信是哪台电脑寄出的。

    优先读 COMPUTERNAME（就是「网上邻居 / 系统属性」里显示的那个名字），
    取不到再退 socket.gethostname()。两者都拿不到时给个中性词，
    总之不返回空串，免得抬头变成「【】」这种半吊子样子。
    """
    for key in ("COMPUTERNAME", "HOSTNAME"):
        name = (os.environ.get(key) or "").strip()
        if name:
            return name
    try:
        import socket
        name = (socket.gethostname() or "").strip()
        if name:
            return name
    except Exception:                 # noqa: BLE001
        pass
    return "本机"


def sanitize_signature(text):
    """
    净化抬头。换行必须去掉 —— 抬头会进邮件的 From 和 Subject，
    里面混进 \\r\\n 就等于让使用者往邮件头里注入任意字段。
    """
    return (text or "").replace("\r", "").replace("\n", "").strip()


def build_notify_task(nd, secret, token, subject, body, recipient, from_name=""):
    """
    拼出交给 mailer 的任务文件内容 —— 任务文件的形状只有这一处定义。

    为什么要抽成函数：早先 _spawn_mailer 写的是 task["smtp"]["user"]，
    而 mailer 那边读的是 task["user"]，两边各自看都自洽，
    合起来却抛 KeyError('user')。把「写」的一方收拢成唯一来源，
    测试只要拿这个函数的产出喂给 mailer，接口对不上就瞒不住了。
    """
    nd = nd or {}
    return {
        "token": token,
        "smtp": {
            "host": (nd.get("host") or "").strip(),
            "port": int(nd.get("port") or 465),
            "use_ssl": bool(nd.get("use_ssl", True)),
            "user": (nd.get("user") or "").strip(),
            "password": ((secret or {}).get("smtp_password") or "").strip(),
        },
        "to": (recipient or "").strip(),
        # 抬头：mailer 拿它当发件人的显示名，收件箱里一眼能看出是哪台机器
        "from_name": sanitize_signature(from_name),
        "subject": subject,
        "body": body,
    }


def hex_to_rgb(color):
    color = (color or "#000000").lstrip("#")
    if len(color) == 3:
        color = "".join(ch * 2 for ch in color)
    try:
        return tuple(int(color[i:i + 2], 16) for i in (0, 2, 4))
    except ValueError:
        return (0, 0, 0)


def mix(c1, c2, ratio):
    """在两色之间插值，ratio=0 取 c1，ratio=1 取 c2。"""
    a, b = hex_to_rgb(c1), hex_to_rgb(c2)
    return "#%02X%02X%02X" % tuple(
        max(0, min(255, round(a[i] + (b[i] - a[i]) * ratio))) for i in range(3)
    )


def shichen_name(hour):
    """把 24 小时制小时换算成十二时辰。"""
    return CN_SHICHEN[((hour + 1) // 2) % 12]


def pretty_target(dt):
    """把 datetime 渲染成直白写法，例如「10月1日 11:30」。

    早先这里写的是古风「十月初一 · 午时」，看着有意境，实际是个坑：
    「正月 / 冬月 / 腊月 / 初一 / 廿五」是农历的专用叫法，公历 12 月 25 日
    被显示成「腊月廿五」，可真正的农历腊月廿五在另一个月份，用户自然会以为
    倒计时算错了。程序里从来没有农历换算（也没打算做），纯属文案撞车。

    顺带修掉一个必崩的 bug：老写法查的是 CN_DAYS 表，那张表只写到「三十」
    （31 项，下标 0~30），于是**任何一个 31 号都会 IndexError**——
    而 12.31 跨年倒计时恰恰是这个挂件最经典的用法。改用数字直接拼，
    天然覆盖到 31 号。

    年份只在「不是今年」时才补上（「2027年1月1日 0:00」）：跨年目标若不写
    年份，用户看不出到底是哪一年的 1 月 1 日；同年目标则不必啰嗦。
    秒为 0 时省略，避免「0:00:00」这种无意义的尾巴。
    """
    if not dt:
        return "尚未设定"
    if dt.year != datetime.datetime.now().year:
        head = "%d年%d月%d日" % (dt.year, dt.month, dt.day)
    else:
        head = "%d月%d日" % (dt.month, dt.day)
    hm = "%d:%02d" % (dt.hour, dt.minute)
    if dt.second:
        hm += ":%02d" % dt.second
    return "%s %s" % (head, hm)


# --------------------------------------------------------------------------
# 在线升级
# --------------------------------------------------------------------------
#
# 这一节的所有 import 都写在函数内部（延迟导入）。
# 理由是本程序的立身之本就是「空闲 CPU ≈ 0、冷启动 < 0.5 秒」：
# urllib 这套东西一导入就要几毫秒外加常驻内存，而绝大多数用户
# **永远不会点**「检查更新」。没必要让所有人替少数人付这份开销。

def version_tuple(text):
    """把 "1.10" 拆成 (1, 10)。比较两个版本用元组，别用字符串。"""
    parts = []
    for chunk in str(text or "").split("."):
        m = re.match(r"\d+", chunk.strip())
        parts.append(int(m.group()) if m else 0)
    while len(parts) < 2:
        parts.append(0)
    return tuple(parts[:4])


def update_available(remote_version):
    """远端版本比本地新，才叫「有更新」。降级或持平均返回 False。"""
    try:
        return version_tuple(remote_version) > version_tuple(APP_VERSION)
    except (TypeError, ValueError):
        return False


def _http_get(url, timeout=UPDATE_CONNECT_TIMEOUT, max_bytes=None,
              headers=None, progress=None):
    """
    取一个 URL 的内容。返回 (bytes, None) 或 (None, 错误文案)。

    progress(已读字节, 总字节) 会被周期性回调，用来在界面上显示进度；
    总字节拿不到时传 -1（服务器没给 Content-Length）。
    """
    import urllib.request
    import urllib.error

    req = urllib.request.Request(url)
    # 注意：HTTP 头按 latin-1 编码，塞中文（APP_NAME）会直接 UnicodeEncodeError，
    # 所以 UA 必须用纯 ASCII 的英文项目名。
    req.add_header("User-Agent", "AncientCountdown/%s" % APP_VERSION)
    for k, v in (headers or {}).items():
        req.add_header(k, v)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            total = -1
            try:
                total = int(resp.headers.get("Content-Length") or -1)
            except (TypeError, ValueError):
                total = -1
            if max_bytes and total > max_bytes:
                return None, "返回内容过大（%d 字节），不像正常的版本信息" % total
            chunks = []
            got = 0
            while True:
                piece = resp.read(65536)
                if not piece:
                    break
                chunks.append(piece)
                got += len(piece)
                if max_bytes and got > max_bytes:
                    return None, "返回内容过大，已中断下载"
                if progress:
                    progress(got, total)
            return b"".join(chunks), None
    except Exception as e:                       # 网络异常种类太多，一律收口
        return None, _net_error_text(e)


def _net_error_text(exc):
    """把网络异常的英文报错翻成人话。用户看不懂 URLError，但看得懂「连不上」。"""
    import urllib.error
    name = type(exc).__name__
    if isinstance(exc, urllib.error.HTTPError):
        return "服务器返回 %s" % exc.code
    if "timed out" in str(exc).lower() or name == "timeout" or "Timeout" in name:
        return "连接超时（%d 秒没响应），多半是网络不通" % UPDATE_CONNECT_TIMEOUT
    if "getaddrinfo" in str(exc) or "Name or service" in str(exc):
        return "找不到服务器地址，检查网络连接"
    return "%s：%s" % (name, exc)


def fetch_update_info(progress=None):
    """
    取最新版本信息，统一成内部格式再返回。

    返回 (info_dict, None) 或 (None, 错误文案)。info_dict 至少含：
        version / notes / size / sha256 / urls(按优先级排好的下载地址列表)

    两个通道都试一遍：CNB（国内，快）在先，GitHub API 在后。
    只要有一个成功就够 —— 查询只是想知道「有没有新版」，
    拿不到就老老实实告诉用户检查失败，不做任何猜测。
    """
    import json as _json

    # ① CNB 上的 version.json（主通道，国内直连）
    data, err = _http_get(UPDATE_INFO_CNB,
                          max_bytes=UPDATE_MAX_INFO_BYTES,
                          headers={"Accept": "application/json"},
                          progress=progress)
    if data:
        try:
            info = _json.loads(data.decode("utf-8", "replace"))
        except Exception:
            info = None
        if isinstance(info, dict) and info.get("version"):
            urls = [u for u in (info.get("cnb_url"), info.get("github_url")) if u]
            # 兜底一条：按 tag 拼出 CNB 的附件地址。
            # version.json 里那两条地址是发版脚本拼的，错一个字母就是 404 ——
            # v1.4 真踩过：附件叫 AncientCountdown_v1.4.zip，脚本写成了
            # _1.4.zip，两条地址全废，用户能看到新版却下不下来。
            # 这条按约定从 tag 拼，多一道保险；就算拼错了也不要紧，
            # download_update 会拿 size/sha256 把它拦下来。
            _tag = str(info.get("tag") or "").strip()
            if _tag:
                urls.append(UPDATE_FALLBACK_CNB % (_tag, _tag))
            if urls:
                return {
                    "version": str(info.get("version")),
                    "tag": str(info.get("tag") or info.get("version")),
                    "notes": info.get("notes") or "",
                    "size": info.get("size") or 0,
                    "sha256": info.get("sha256") or "",
                    "urls": urls,
                    "source": "CNB",
                }, None
        err = "版本信息格式不对"

    # ② GitHub Release API（备用通道）
    data, err2 = _http_get(UPDATE_INFO_GITHUB_API,
                           max_bytes=UPDATE_MAX_INFO_BYTES,
                           headers={"Accept": "application/vnd.github+json"},
                           progress=progress)
    if data:
        try:
            rel = _json.loads(data.decode("utf-8", "replace"))
        except Exception:
            rel = None
        if isinstance(rel, dict) and rel.get("tag_name"):
            tag = str(rel["tag_name"])
            urls = []
            for a in (rel.get("assets") or []):
                u = a.get("browser_download_url")
                if u:
                    urls.append(u)
            if not urls:
                return None, "GitHub 上的新版没有可下载的附件"
            # CNB 同版本包通常也在，拼一个放最前面，让下载也尽量走国内
            ver = tag.lstrip("vV")
            urls.insert(0, UPDATE_FALLBACK_CNB % (tag, tag))
            return {
                "version": ver,
                "tag": tag,
                "notes": rel.get("body") or "",
                "size": (rel.get("assets") or [{}])[0].get("size") or 0,
                "sha256": "",          # GitHub API 不直接给附件的 sha256
                "urls": urls,
                "source": "GitHub",
            }, None

    return None, err2 or err or "检查更新失败，请检查网络连接"


AFTER_UPDATE_ARG = "--after-update"   # 更新后由旧版本拉起新版本时带的标记


def download_update(info, progress=None):
    """
    把新版发布包下载到临时目录，并校验大小和 sha256。

    返回 (zip 路径, None) 或 (None, 错误文案)。

    校验这一步不能省：下载走的是公网，中途被篡改或下到一半断了，
    拿一个坏包去替换正在运行的程序，等于把用户手里的东西直接毁掉。
    有 sha256 就比 sha256（强校验），没有（走 GitHub 备用通道时拿不到）
    也比一下文件大小 —— 弱，但总比什么都不查强。
    """
    import tempfile

    errs = []
    for url in info.get("urls") or []:
        fd, path = tempfile.mkstemp(prefix="anc_upd_", suffix=".zip")
        os.close(fd)
        keep = False             # 只有校验通过的包才留下，其余一律删掉
        try:
            data, err = _http_get(url, timeout=60, progress=progress)
            if not data:
                errs.append("%s（%s）" % (err, _host_of(url)))
                continue
            with open(path, "wb") as f:
                f.write(data)

            want_size = info.get("size") or 0
            if want_size and len(data) != want_size:
                errs.append("文件大小对不上（应 %d，实 %d）" % (want_size, len(data)))
                continue

            want_hash = (info.get("sha256") or "").strip().lower()
            if want_hash:
                got = hashlib.sha256(data).hexdigest()
                if got != want_hash:
                    errs.append("校验码对不上，文件可能被改动过，已放弃")
                    continue
            keep = True
            return path, None
        finally:
            # 收尾必须用 keep 标记，不能靠「文件存在且非空」来判断：
            # 大小 / sha256 校验失败时文件已经写进去了，那个条件不成立，
            # 坏包就永远留在 %TEMP% 里（每个 11 MB，试几条地址就堆几十兆）。
            if not keep:
                try:
                    os.remove(path)
                except OSError:
                    pass
    return None, "下载失败：" + "；".join(errs[:2])


def _host_of(url):
    """从 URL 里抠出主机名，报错时告诉用户是哪条路不通。"""
    m = re.match(r"https?://([^/]+)", str(url or ""))
    return m.group(1) if m else "未知地址"


def extract_exe(zip_path, workdir):
    """
    从发布包里把 exe 取出来。返回 (exe 路径, None) 或 (None, 错误文案)。

    发布包里除了 exe 还有使用说明、发信脚本等，只认 .exe 结尾的那一个。
    解压用 zipfile 自己的 extract，不手写读流 —— 手写容易在
    Zip Slip（条目名里带 ../）这类路径穿越上翻车。
    """
    import zipfile

    try:
        with zipfile.ZipFile(zip_path) as zf:
            names = [n for n in zf.namelist() if n.lower().endswith(".exe")]
            if not names:
                return None, "压缩包里没有找到 exe 程序"
            name = names[0]
            zf.extract(name, workdir)
            exe = os.path.join(workdir, name)
            if not os.path.exists(exe) or os.path.getsize(exe) < 100000:
                return None, "取出的程序文件不完整"
            return exe, None
    except Exception as e:
        return None, "解压失败：%s" % e


def install_update(new_exe_path):
    """
    用新 exe 换掉**正在运行的自己**，然后拉起新版本。

    这是整个功能里最需要小心的一步。Windows 上正在运行的 exe：
        · **不能删除**（实测 PermissionError）
        · **不能覆盖**
        · **但可以重命名**（实测可以）
    于是流程设计成：
        1. 新 exe 先复制到「程序所在目录」的临时文件（同盘，保证移动是原子的）
        2. 正在运行的自己改名成 xxx.exe.old  ← 这一步是关键，腾出原文件名
        3. 临时文件就位成 xxx.exe
        4. 启动新的 xxx.exe（带 --after-update 标记）
        5. 调用方退出旧进程
    全程不需要 cmd / bat 脚本 —— 中文路径（「古风倒计时.exe」）交给
    命令行解释器处理很容易在编码上翻车，纯 Python 做就没有这问题。

    第 3 步万一失败会把第 2 步回滚，绝不留一个「程序不见了」的现场。
    .old 不会立刻删掉（它是用户唯一的退路）：要等新版连续稳定启动满
    UPDATE_GUARD_RUNS 次，才由 note_successful_run 清掉。

    返回 (True, None) 或 (False, 错误文案)。
    """
    import subprocess

    if not getattr(sys, "frozen", False):
        return False, "当前是以脚本方式运行，不能自我更新（请运行打包好的 exe）"

    target = os.path.abspath(sys.executable)
    workdir = os.path.dirname(target)
    old_path = target + UPDATE_OLD_SUFFIX

    # 预检：目录能不能写。放在最前面，免得走到一半才发现没权限，
    # 那时旧 exe 已经被改名，现场更难收拾。
    try:
        probe = os.path.join(workdir, ".upd_probe_%d" % os.getpid())
        with open(probe, "wb") as f:
            f.write(b"x")
        os.remove(probe)
    except Exception as e:
        return False, ("程序所在目录没有写入权限，无法更新。\n"
                       "请把 exe 放到普通文件夹里（不要放在 C:\\Program Files），"
                       "或右键以管理员身份运行后再试。\n（%s）" % e)

    staged = os.path.join(workdir, ".upd_new_%d.exe" % os.getpid())
    try:
        shutil.copyfile(new_exe_path, staged)
        # 旧 exe 正在运行：只能改名，不能删。改完原文件名就空出来了。
        os.replace(target, old_path)
        try:
            os.replace(staged, target)
        except Exception:
            os.replace(old_path, target)     # 回滚：把旧版本放回去
            raise
    except Exception as e:
        try:
            if os.path.exists(staged):
                os.remove(staged)
        except OSError:
            pass
        return False, "更新失败，程序保持原样：%s" % e

    try:
        # 关键：清掉 PyInstaller onefile 的内部环境变量（_PYI_*）。
        # 新版 bootloader 会凭这些变量校验「发起方父进程」，而本进程
        # 是即将退出的旧实例、镜像刚被改名 —— 校验对不上，
        # 新进程会弹「Security validation failure」然后拒绝启动。
        # 给新进程一份干净环境，它就当自己是被用户正常双击启动的。
        env = dict(os.environ)
        for key in [k for k in env if k.startswith("_PYI")]:
            env.pop(key)
        subprocess.Popen([target, AFTER_UPDATE_ARG], cwd=workdir, env=env)
    except Exception as e:
        # 程序已经换成新的了，只是没自动起来 —— 告诉用户手动双击即可
        return False, "新版本已就位，但没能自动启动：%s\n请手动双击 %s" % (e, target)
    return True, None


def wait_for_instance_lock(timeout=20.0):
    """
    更新后重启专用：等旧进程把单实例锁交出来。

    为什么需要它：旧进程拉起新进程之后才会退出，那一瞬间互斥体还握在
    旧进程手里。新进程一取锁就以为「已经有一个在跑」，于是按老规矩
    唤醒它再自己退出 —— 可那个「已有实例」马上就要死了，
    最终结果是程序彻底消失。带上 --after-update 标记的新进程走这条路，
    轮询等锁，等到就正常启动。
    """
    deadline = time.time() + timeout
    while time.time() < deadline:
        time.sleep(0.4)
        if acquire_single_instance():
            return True
    return False


def delete_old_exe_async():
    """
    后台慢慢删掉更新留下的 .old 文件。

    必须是异步的：新进程启动时旧进程往往还没死透，.old 仍被占用，
    这时删必然失败。要是放在启动路径上同步重试，启动就得卡好几秒，
    这和本程序「冷启动 < 0.5 秒」的底线冲突。丢给守护线程慢慢来，
    删不掉也无所谓，下次启动再试。
    """
    import threading

    def worker():
        old = os.path.abspath(sys.executable) + UPDATE_OLD_SUFFIX
        for _ in range(24):                  # 最多等约 12 秒
            if not os.path.exists(old):
                return
            try:
                os.remove(old)
                return
            except OSError:
                time.sleep(0.5)

    if getattr(sys, "frozen", False):
        t = threading.Thread(target=worker, daemon=True)
        t.start()


def guard_step(guard, version, needed=UPDATE_GUARD_RUNS):
    """
    算出「这一次启动之后该记成第几次」，以及要不要动 .old。

    单独抽出来是因为它是这套机制里唯一有分支的地方（版本换了要重新数），
    而删文件那一步在脚本模式下跑不了（见下）。把判定和动作分开，
    规则就能被测试钉住，不必真的去删一个 exe。

    返回 (新计数, 是否该删 .old)。
    """
    runs = 0
    # 版本对不上就从头数：换了一版就该重新给用户三回机会
    if isinstance(guard, dict) and guard.get("version") == version:
        try:
            runs = int(guard.get("ok_runs") or 0)
        except (TypeError, ValueError):
            runs = 0
    runs += 1
    return runs, runs >= needed


def note_successful_run():
    """
    新版本稳定启动了一次 —— 记一笔；攒够次数才把 .old 删掉。

    为什么不当场删（早先就是这么干的，已改）：那个 .old 是用户唯一的回滚手段，
    删早了等于把退路提前烧掉 —— 新版「起来了但功能不对」的时候，
    用户连把 .old 改回 .exe 的机会都没有。

    计数必须落注册表：它是跨进程、跨重启的状态，放内存里一关就忘光了。
    调用点在启动满 UPDATE_GUARD_DELAY_MS 之后（见 CountdownApp 的定时器），
    于是「新版本启动几十秒内就崩」那种情况根本走不到这里 —— 这一笔不算数，
    计数停在原地，.old 留着。正是我们想要的。
    """
    if not getattr(sys, "frozen", False):
        return
    old = os.path.abspath(sys.executable) + UPDATE_OLD_SUFFIX
    if not os.path.exists(old):
        # 没有旧版本可回滚（首次安装，或上次已经清干净）—— 顺手清掉计数残留
        reg_store_delete(UPDATE_GUARD_KEY)
        return

    guard = reg_store_read(UPDATE_GUARD_KEY, {})
    runs, should_delete = guard_step(guard, APP_VERSION)

    if should_delete:
        # 删成功才清计数。删不掉就留着计数下次启动接着试，
        # 免得又要从头攒三回。
        try:
            os.remove(old)
        except OSError:
            reg_store_write(UPDATE_GUARD_KEY,
                            {"version": APP_VERSION, "ok_runs": runs})
            return
        reg_store_delete(UPDATE_GUARD_KEY)
        return

    reg_store_write(UPDATE_GUARD_KEY, {"version": APP_VERSION, "ok_runs": runs})


def last_auto_check_ts():
    """上次自动检查真的查通了的时间戳；没查过返回 0。"""
    rec = reg_store_read(UPDATE_CHECK_KEY, {})
    if not isinstance(rec, dict):
        return 0.0
    try:
        return float(rec.get("last_ts") or 0)
    except (TypeError, ValueError):
        return 0.0


def remembered_new_version():
    """
    上次自动检查看到的线上版本号 —— 但它**只有确实比本机新**才算数。

    这个判据顺带解决了一件事：用户升级完成之后 APP_VERSION 就跟着变了，
    这里自然返回空，右上角那颗小红点自己就消失，
    不需要任何额外的清理动作，也就没有「红点擦不掉」的可能。
    """
    rec = reg_store_read(UPDATE_CHECK_KEY, {})
    if not isinstance(rec, dict):
        return ""
    ver = str(rec.get("version") or "")
    return ver if update_available(ver) else ""


def note_auto_check(ver):
    """记下「自动检查过了」：时间戳用来限频，版本号用来点亮小红点。"""
    reg_store_write(UPDATE_CHECK_KEY,
                    {"last_ts": time.time(), "version": str(ver or "")})


def log_problem(tag, exc_type, exc_value, exc_tb):
    """
    把一条异常写进崩溃日志 —— windowed exe 唯一的「留痕」手段。

    为什么非要自己动手：`--windowed` 打包出来没有控制台，而 Tk 的 after
    回调里抛出的异常会被它默认的 report_callback_exception 悄悄丢掉，
    连 PyInstaller 那个 Error 弹框都不会出现。表现就是「窗口还开着，
    但数字不走了」，且一点线索都不留。这种事只能靠主动接管来暴露。

    界面上一个字都不写：这些都是后台的杂事，用户没要求、也不该被打扰。
    """
    import traceback
    try:
        path = os.path.join(tempfile.gettempdir(), "ac_crash.log")
        with open(path, "a", encoding="utf-8") as f:
            f.write("\n[%s] %s\n" % (tag, _stamp()))
            traceback.print_exception(exc_type, exc_value, exc_tb, file=f)
    except Exception:                         # noqa: BLE001
        pass


def note_scan_error(exc):
    """自动检查更新踩了坑 —— 交给上面那个统一的留痕函数。"""
    log_problem("自动检查更新", type(exc), exc, exc.__traceback__)


SELFUPDATE_RESULT_FILE = "ac_selfupdate_result.txt"


def run_selfupdate_cli():
    """
    无界面的自我更新：古风倒计时.exe selfupdate

    与设置面板里「检查更新」按钮走**完全相同**的函数链
    （fetch_update_info -> download_update -> extract_exe -> install_update），
    只是把弹窗换成写结果文件 —— .pyw 没有控制台，print 什么都看不见。

    存在的理由有两个：
      · 测试：替换流程必须拿真 exe 在真机上走一遍，而 GUI 弹窗无法脚本驱动；
      · 批量：十几台机器挨个点按钮也累，有了命令行就能写个循环脚本一键全升。

    结果文件放在 %TEMP%，逐阶段覆写 —— 中途崩了也能看到死在哪一步。
    退出码：0 = 无事发生或成功，1 = 失败。
    """
    import tempfile

    rf = os.path.join(tempfile.gettempdir(), SELFUPDATE_RESULT_FILE)

    def note(msg):
        try:
            with open(rf, "w", encoding="utf-8") as f:
                f.write(msg)
        except OSError:
            pass

    note("查询版本信息…")
    info, err = fetch_update_info()
    if err or not info:
        note("FAIL 查询失败：%s" % err)
        return 1
    if not update_available(info.get("version")):
        note("OK 已是最新版本 v%s（线上 v%s）" % (APP_VERSION, info.get("version")))
        return 0
    note("发现新版本 v%s（来自 %s），下载中…" % (info.get("version"),
                                                info.get("source")))
    zip_path, err = download_update(info)
    if not zip_path:
        note("FAIL 下载失败：%s" % err)
        return 1
    workdir = tempfile.mkdtemp(prefix="anc_upd_cli_")
    exe, err = extract_exe(zip_path, workdir)
    if not exe:
        note("FAIL 解压失败：%s" % err)
        return 1
    note("校验通过，正在替换程序…")
    ok, err = install_update(exe)
    if not ok:
        note("FAIL 更新失败：%s" % err)
        return 1
    note("OK 已更新到 v%s，新版本已启动" % info.get("version"))
    return 0


def _time_error(hour, minute):
    """报错时把用户原样写的数字带回给他，别让他自己回去数第几段填错了。"""
    return "时间需在 0 ~ 23 时 0 ~ 59 分之间，你写的是 %d 时 %d 分" % (hour, minute)


def _lenient(hour, minute, second):
    """宽松读法：时/分/秒越界时退回 0。

    只有一个场景配用这种读法：**整条输入凑巧能解释成「年份 + 月日时分」**，
    也就是必须动用"第一位是年份"才能读通的时候。
      "10.1.8.5"  月份 10 读法读不通（时分是 8:5 但第二位 5 越界？不，是月1日8:5
                  看着也通）—— 真正需要它的是 "10.1.11.30" 被误当年份后的兜底。
    普通输入（"10.1 24"）绝不宽松：时 24 就是写错了，必须报错。
    否则用户把 24 点敲进去，程序会默默改成 0 点，倒计时差一整天。
    """
    return (hour if 0 <= hour <= 23 else 0,
            minute if 0 <= minute <= 59 else 0,
            second if 0 <= second <= 59 else 0)


def _resolve_year(month, day, hour, minute, second, now, noisy):
    """年份确定的两种收尾，区别只在「读不通时怎么办」。

    不写年份时，挑「下一个还没到的」那一年（含今年）。
    """
    if noisy:
        for y in (now.year, now.year + 1, now.year + 2):
            try:
                candidate = datetime.datetime(y, month, day, hour, minute, second)
            except ValueError:
                continue                   # 例：2月29日在平年不存在，跳到闰年
            if candidate > now:
                return candidate, None
        return None, "在接下来三年内找不到该日期，请检查月日"

    for y in (now.year, now.year + 1, now.year + 2):
        try:
            candidate = datetime.datetime(y, month, day, hour, minute, second)
        except ValueError:
            continue
        if candidate > now:
            return candidate, None
    # 整条输入都不成立时才明确报错 —— 到这一步说明月份、日期都越界了
    if not 1 <= month <= 12:
        return None, "在接下来三年内找不到该日期，请检查月日"
    return None, "在接下来三年内找不到该日期，请检查月日"


# 年份提示的判定范围：只有「像这几年的年份」才值得提醒一句。
#
# 为什么不是 1000~9999：四位数字只要 ≤ 2359 就同时是合法的「时时:分分」，
# 所以 "1900"、"2100" 这些既像年份又像时间（19:00 / 21:00），
# 而**时间才是这一段的默认含义**（年份按规定要写在最前面）。
# 只有落在「现在前后这几年」里的数字，才真有可能是用户想写年份 ——
# 那时候随口提一句，比事后让他自己发现倒计时差了一天强。
YEAR_HINT_BACK = 1
YEAR_HINT_FORWARD = 10


def looks_like_recent_year(text, now=None):
    """这个四位数是不是「像最近几年的年份」（只用于给一句提示，不参与解析）。"""
    s = str(text or "").strip()
    if len(s) != 4 or not s.isdigit():
        return False
    now = now or datetime.datetime.now()
    y = int(s)
    return now.year - YEAR_HINT_BACK <= y <= now.year + YEAR_HINT_FORWARD


def _split_clock(text):
    """
    把揉在一起的时分秒拆成 [时, 分, 秒?]；拆不出来返回 None。

        0330    -> [3, 30]       四位：时时 分分
        033000  -> [3, 30, 0]    六位：时时 分分 秒秒
        130     -> [1, 30]       奇数位：第一位单独当「时」，后面两两分组
        13030   -> [1, 30, 30]

    拆不出来（位数不在 3~6、或拆完越界）一律返回 None，让上层按原样去读、
    该报错就报错 —— 宁可换来一句「时间需在 0 ~ 23 时」，也不要猜出一个
    看着合理的错时间。这和「13.1 不能猜成 2013 年」是同一条规矩。
    """
    s = str(text or "").strip()
    if not s.isdigit() or not 3 <= len(s) <= 6:
        return None
    if len(s) % 2:                       # 奇数位：第一位单独当「时」
        groups = [s[0]] + [s[i:i + 2] for i in range(1, len(s), 2)]
    else:
        groups = [s[i:i + 2] for i in range(0, len(s), 2)]
    parts = [int(g) for g in groups]
    hh = parts[0]
    mm = parts[1] if len(parts) > 1 else 0
    ss = parts[2] if len(parts) > 2 else 0
    if not (0 <= hh <= 23 and 0 <= mm <= 59 and 0 <= ss <= 59):
        return None
    return parts


def _expand_compact_time(toks):
    """
    摊开「时」那一段（下标 2）里揉着的写法，返回新的字符串列表。

        ["10", "1", "0330"]          -> ["10", "1", "03", "30"]
        ["10", "1", "033000"]        -> ["10", "1", "03", "30", "00"]
        ["2026", "10", "1", "1130"]  -> ["2026", "10", "1", "11", "30"]

    只动这一段：前两段是月、日；四位数的年份也压根不在这个位置上
    （"2026.10.1" 的第一段才是年份）。月、日那两段绝不动 ——
    否则 "10 1 0330" 里的 "10" 会被当成 1 时 0 分，整条读法全乱。
    """
    out = list(toks)
    if len(out) <= 2:
        return out
    parts = _split_clock(out[2])
    if parts:
        out[2:3] = ["%02d" % v for v in parts]
    return out


def parse_target(text, now=None):
    """
    解析目标时刻 —— 只认数字，数字之间填什么当分隔都行。

        "10.1.11.30"        10月1日 11:30
        "10 1 2  32"        同上（空格、点半角全角、逗号斜杠破折号一概当分隔）
        "10.1/2，32"        同上
        "10 1 0330"         10月1日 03:30（时分揉在一个数字里也认）
        "10.1.1130"         10月1日 11:30
        "10 1 033000"       10月1日 03:30:00
        "2026.10.1.11.30"   显式指定年份
        "26.10.1"           年份写两位也行

    依次按 [年?] 月 日 时 分 秒 读；少写尾巴就是 0，所以 "10.1" 是当日零点。
    返回 (datetime | None, 错误提示 | None)
    未指定年份时，自动选择「下一个尚未到来的」那一年。
    """
    now = now or datetime.datetime.now()

    raw = str(text or "").strip()
    if not raw:
        return None, "请输入目标时间，例如 10.1.11.30"

    # 非数字一律当分隔符：空格、制表、换行、点半角「.」。全角「．」、
    # 逗号、顿号、斜杠、破折号、下划线、冒号、中文年月日……全都不用特判。
    # 中英文标点在 Unicode 里都不属于 \w，所以一条 \d+ 就够了。
    nums = re.findall(r"\d+", raw)

    # 一个数字都没找到。这一条必须在取 nums[0] 之前挡掉 ——
    # 否则一行 "abc" 就能让整个程序崩掉（实测撞过 IndexError）。
    if not nums:
        return None, "没找到数字。至少要写月和日，例如 10.1"

    # 写死一个数没意义。这不是"分隔符问题"而是少了信息，所以单独说清楚，
    # 免得用户对着「例如 10.1.11.30」反复琢磨自己是不是敲错了标点。
    if len(nums) == 1:
        return None, "只有一个数字「%s」，看不出是什么，至少要写月和日，例如 10.1" % nums[0]

    # 三种读法，顺序就是**优先级**，这一点是这段逻辑的命门：
    #   ① plain   第一位是月份（最常用、也最该优先）
    #   ② year4   第一位是四位年份
    #   ③ year2   第一位是两位年份
    #
    # 为什么"月份"必须排在"两位年份"前面 —— 这是实测踩出来的：
    #   "13.1"     → 用户想写 13 月（明显是想打 1 月 3 日或手误）。
    #                若 year2 优先，会读出 2013年1月1日 —— 一个完全不相干的日子，
    #                而且不报错！用户得看到"✓ 2013年…"才发现不对。
    #   "10.1 24"  → 用户想写 24 点。若 year2 优先，会读出 2010年1月24日。
    # 只有当"按月份读"根本读不通时，才轮到年份出场（例如 "26.10.1"）——
    # 那时 plain 读法会因 26 > 12 作废，year2 自然接上。
    # 顺带一个好处："13.1" 会正常报「月份需在 1~12 之间」，
    # 比给出一个看似合理的错误日期好得多。
    #
    # 曾经还试过第四条「month2」：把个位数开头猜成"月份漏了首位"，
    # 让 "1 10" 读成 1月10日。实测证明是个坏主意 ——
    # "10.1 24" 会被它猜成 2010年1月24日、"13.1" 猜成 2013年1月1日。
    # 它只是把年份那张错答案换了个样子。删掉。
    vals = [int(n) for n in nums]

    readings = []
    if len(nums[0]) == 4:
        readings.append(("year4", vals[0], nums[1:]))
    readings.append(("plain", None, nums))
    if len(nums[0]) == 2:
        y2 = 2000 + vals[0]
        # 两位年份只在「离当年足够近」时才算数。
        #
        # 为什么加这道门槛 —— 这是实测撞出来的最危险的一类错：
        #   "13.1"    用户想写 13 月。按 2013 年读会得到 2013年1月1日，
        #             **不报错**，用户得盯着预览才发现日子完全不对。
        #   "10.1 24" 用户想写 24 点。按 2010 年读会得到 2010年1月24日。
        # 这两条里年份读法只是"碰巧合法"，它给出的答案离用户本意十万八千里。
        # 而"写两位年份"这个动作本身意味着「就是近些年」——
        # 正常人不会用两位写一个十六年前的年份。所以窗口取 ±8 年。
        # 挡掉之后，"13.1" 会落到错误提示「月份需在 1~12 之间」，
        # 比一个看着合理的错误日期好得多。
        if now.year - 8 <= y2 <= now.year + 8:
            readings.append(("year2", y2, nums[1:]))

    for kind, year, rest in readings:
        if not rest:
            continue
        # 时间那一段可能被揉在一个数字里（"10 1 0330" 的第三段）。
        # 摊开放在这里做，是因为「哪一段是时」要看了读法才知道：
        # plain 读法的月日在 rest[0]、rest[1]，年份读法同样如此 ——
        # 两种情况下「时」都在 rest[2]，所以摊开的位置一致。
        rest = [int(t) for t in _expand_compact_time(rest)]
        mo, dy = rest[0], (rest[1] if len(rest) > 1 else 1)
        hr = rest[2] if len(rest) > 2 else 0
        mi = rest[3] if len(rest) > 3 else 0
        se = rest[4] if len(rest) > 4 else 0
        sane = (1 <= mo <= 12 and 1 <= dy <= 31
                and 0 <= hr <= 23 and 0 <= mi <= 59 and 0 <= se <= 59)

        if kind in ("year4", "year2"):
            # 年份读法必须**整条都合法**才成立。否则 "2026.2.29" 这种
            # 不存在的日期会被当成"年份 2026 + 月 2 + 日 29 读不通"，
            # 然后错误地回落到把 2026 当月份。
            if not sane:
                continue
            try:
                return datetime.datetime(year, mo, dy, hr, mi, se), None
            except ValueError:
                continue

        # 时/分/秒越界只有**年份读法**才有资格宽容一次：
        # "10.1 11 30" 按月份读是 10月1日 11:30（成立）；
        # 按年份读是 2010年1月11日 30分（30 分越界）。
        # 宽松是为了让"年份这条读法"不至于把整条输入拖死，
        # 绝不能让普通读法也宽容 —— 那会把 "3.1 24" 的 24 点悄悄改成 0 点。
        if not sane:
            if kind == "year2":
                hr, mi, se = _lenient(hr, mi, se)
            else:
                continue

        # 月份/日越界：这条读法作废
        if not (1 <= mo <= 12 and 1 <= dy <= 31):
            continue

        got, _ = _resolve_year(mo, dy, hr, mi, se, now, noisy=False)
        if got is not None:
            return got, None

    # 全试完了还是读不通 —— 这时才值得报错，并且尽量指出是哪一段越界。
    # 注意要从「年份读法」之后的位置看：四位数开头说明第一位是年份，
    # 那月份应该在 vals[1]。
    idx = 1 if len(nums[0]) == 4 and len(vals) > 1 else 0
    if not 1 <= vals[idx] <= 12:
        return None, "月份需在 1 ~ 12 之间，你写的是 %d" % vals[idx]
    if len(vals) > idx + 1 and not 1 <= vals[idx + 1] <= 31:
        return None, "日期需在 1 ~ 31 之间，你写的是 %d" % vals[idx + 1]
    if len(vals) > idx + 2 and not 0 <= vals[idx + 2] <= 23:
        return None, _time_error(vals[idx + 2], vals[idx + 3] if len(vals) > idx + 3 else 0)
    if len(vals) > idx + 3 and not 0 <= vals[idx + 3] <= 59:
        return None, _time_error(vals[idx + 2], vals[idx + 3])
    if len(vals) > idx + 4 and not 0 <= vals[idx + 4] <= 59:
        return None, "秒需在 0 ~ 59 之间，你写的是 %d" % vals[idx + 4]
    return None, "「%s」不是个成立的日期，请检查月日" % raw


def pick_theme(remaining_seconds, cfg):
    """
    根据剩余秒数挑出当前配色。
    规则按 days 升序排列，第一个满足「剩余 <= 阈值」的就是最紧迫的一档。
    """
    pal = cfg["palette"]
    rules = []
    for item in cfg.get("thresholds", []):
        try:
            days = float(item.get("days"))
        except (TypeError, ValueError):
            continue
        rules.append((days, item))
    rules.sort(key=lambda pair: pair[0])

    for days, item in rules:
        if remaining_seconds <= days * 86400.0:
            return {
                "fg": (item.get("color") or pal["default_fg"]).strip(),
                "bg": (item.get("bg") or pal["paper"]).strip(),
                "bg_explicit": bool(item.get("bg")),
                "label": item.get("label") or "",
            }
    return {"fg": pal["default_fg"], "bg": pal["paper"],
            "bg_explicit": False, "label": ""}


# --------------------------------------------------------------------------
# 主窗口
# --------------------------------------------------------------------------

class CountdownApp:

    def __init__(self):
        self.cfg = load_config()
        self.target, self.parse_err = parse_target(self.cfg.get("target"))

        self.remaining = None
        self.zero_mode = False
        self.theme = None
        self.blink = False
        self._last_text = None

        # 传书状态：这里只持有内存里的引用，不读文件也不发网络请求，
        # 所以对启动速度和常驻占用都没有影响
        self.secret = load_notify_secret()
        self.notify_state = load_notify_state()
        self._last_notify_check = 0.0
        self._notify_note = ""          # 最近一次传书结果，说给用户听
        self._notify_note_at = 0.0

        # 字号缓存：字体切换在 Tk 中约 8ms，必须避免每秒重新试错
        self._digits_key = None
        self._digits_size = 100
        self._zero_key = None
        self._zero_size = 100

        self._ctl_hover = ""            # 右上角三个小按钮里，鼠标正压着哪一个
        self._ctl_pos = {}              # 绘制时算好的按钮坐标，命中判定读它
        self._settings = None

        # 自动检查更新的状态全部落在注册表：限频时间戳、上次看到的线上版本。
        # 这里只读两个值，毫秒级，对启动速度没有可感影响；
        # new_version 必须赶在 _place_window 之前定好，因为右上角那颗小红点
        # 是随窗口重绘一起画出来的。
        self.new_version = remembered_new_version()
        self._update_scan_at = time.time() + UPDATE_AUTO_START_DELAY

        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.overrideredirect(True)               # 无系统边框，纯自绘
        # windowed exe 没有控制台，Tk 回调里抛出的异常默认会被悄悄丢掉
        # （表现成「窗口还开着，数字不走了」，却查不出任何原因）。接管它。
        self.root.report_callback_exception = self._on_tk_error
        pal = self.cfg["palette"]
        self.root.configure(bg=pal["ink"])
        self.root.attributes("-topmost", bool(self.cfg.get("always_on_top", True)))

        self.canvas = tk.Canvas(self.root, highlightthickness=0, bd=0,
                                bg=pal["paper"], cursor="fleur")
        self.canvas.pack(fill="both", expand=True)

        # 状态变量：必须先于 _place_window 初始化。
        # 否则刚算好的位置和尺寸会被下面几行覆盖成 0 —— 命中判定随之失效
        # （点哪儿都被当成拖边缘）、拖拽再基于 (0,0,0,0) 去算，越拖越负，
        # 最终把窗口丢到屏幕外并写进配置文件。
        self.W = self.H = 0
        self.x = self.y = 0
        self.w = self.h = 0
        self._drag_mode = ""
        self._press_pt = (0, 0)
        self._press_geo = (0, 0, 0, 0)
        self._dragging = False

        self._build_fonts()
        self._place_window()

        self._bind_events()
        self._build_menu()

        self.root.update_idletasks()
        self.layout()
        self.tick()

        # 启动满 60 秒才算「这一次启动成功了」—— 既给新版本留一个暴露崩溃的
        # 机会窗口，也是 .old 保留计数（note_successful_run）唯一的入口。
        self.root.after(UPDATE_GUARD_DELAY_MS, self._note_run_ok)

    # ---------------- 初始化 ----------------

    def _build_fonts(self):
        available = set(tkfont.families())

        def pick(candidates, fallback):
            for name in candidates:
                if name in available:
                    return name
            return fallback

        # 中文：楷体最有书卷气；数字：衬线体（Georgia / Cambria）配楷体很协调
        self.fam_cn = pick(["楷体", "KaiTi", "华文楷体", "STKaiti", "仿宋", "FangSong", "宋体"],
                           "Microsoft YaHei")
        self.fam_num = pick(["Georgia", "Cambria", "Times New Roman", "Constantia"],
                            "Times New Roman")

        self.f_title = tkfont.Font(family=self.fam_cn, size=15)
        self.f_num = tkfont.Font(family=self.fam_num, size=72, weight="bold")
        self.f_unit = tkfont.Font(family=self.fam_cn, size=24, weight="bold")
        self.f_seal = tkfont.Font(family=self.fam_cn, size=15, weight="bold")
        self.f_seal_small = tkfont.Font(family=self.fam_cn, size=9)
        self.f_gear = tkfont.Font(family=self.fam_cn, size=12)
        self.f_hint = tkfont.Font(family=self.fam_cn, size=11)
        self.f_zero = tkfont.Font(family=self.fam_cn, size=64, weight="bold")

    # ---- 位置合法性 ----

    def default_position(self):
        """默认落点：主屏右上角，留一点边距。"""
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        return max(0, sw - self.w - 80), max(0, int(sh * 0.14))

    def visible_area(self, x, y, w=None, h=None):
        """窗口落在真实桌面范围内的可见宽高。"""
        w = self.w if w is None else w
        h = self.h if h is None else h
        vl, vt, vr, vb = screen_rect(self.root)
        return (max(0, min(x + w, vr) - max(x, vl)),
                max(0, min(y + h, vb) - max(y, vt)))

    def clamp_position(self, x, y, w=None, h=None):
        """
        把窗口拉回桌面：保证至少露出 MIN_VISIBLE_W × MIN_VISIBLE_H。
        返回 (x, y, 是否发生修正)。位置本来就合法时原样返回。
        """
        w = self.w if w is None else w
        h = self.h if h is None else h
        vw, vh = self.visible_area(x, y, w, h)
        if vw >= MIN_VISIBLE_W and vh >= MIN_VISIBLE_H:
            return int(x), int(y), False
        vl, vt, vr, vb = screen_rect(self.root)
        # 只动越界的那一个方向，尽量保住用户原本的摆放意图
        nx = min(max(x, vl), max(vl, vr - w))
        ny = min(max(y, vt), max(vt, vb - h))
        return int(nx), int(ny), True

    def _place_window(self, persist=True):
        """
        按存档（或缺省）把窗口摆到该在的位置。

        persist=False 只挪窗口、不落盘 —— 恢复出厂时用它：
        键刚被整个删掉，立刻又写一份默认配置回去，用户开注册表一看
        「怎么还在」，会以为没生效。让它空着，等用户真改了什么再自然落盘。
        """
        win = self.cfg.get("window", {})
        vl, vt, vr, vb = screen_rect(self.root)
        # 尺寸同样要校验：换到更小的屏幕后，旧的大尺寸也会把窗口撑出可视区
        self.w = min(max(MIN_W, int(win.get("w") or 620)), max(MIN_W, vr - vl))
        self.h = min(max(MIN_H, int(win.get("h") or 300)), max(MIN_H, vb - vt))

        x, y = win.get("x"), win.get("y")
        if x is None or y is None:
            x, y = self.default_position()
        else:
            # 存档坐标未必还成立：显示器换过、分辨率改过，
            # 或者上一次就是被拖到屏幕外才退出的。
            x, y, rescued = self.clamp_position(int(x), int(y))
            if rescued:
                # 已经不可见了，就别再贴到某个边缘——那个位置用户从没选过，
                # 直接回到明确的默认落点，免得他满屏幕找窗口。
                x, y = self.default_position()

        self.x, self.y = int(x), int(y)
        self.cfg.setdefault("window", {})
        self.cfg["window"].update({"x": self.x, "y": self.y})
        if persist:
            save_config(self.cfg)
        set_geometry(self.root, self.w, self.h, self.x, self.y)

    def _bind_events(self):
        c = self.canvas
        c.bind("<Button-1>", self._on_press)
        c.bind("<B1-Motion>", self._on_drag)
        c.bind("<ButtonRelease-1>", self._on_release)
        c.bind("<Motion>", self._on_hover)
        c.bind("<Double-Button-1>", lambda e: self.open_settings())
        c.bind("<Button-3>", self._popup_menu)
        c.bind("<Configure>", self._on_configure)
        self.root.bind("<Escape>", lambda e: self.close_settings())
        # 从任务栏恢复时要把系统边框收回去 —— 见 minimize_app / _on_root_map。
        # <Map> 是「窗口重新出现」，<FocusIn> 是兜底：个别情况下任务栏恢复
        # 只触发了焦点变化。两个都挂上，函数内部会先判一次状态，开销可忽略。
        self.root.bind("<Map>", self._on_root_map)
        self.root.bind("<FocusIn>", self._on_root_map)

    def _build_menu(self):
        pal = self.cfg["palette"]
        self.menu = tk.Menu(self.root, tearoff=0,
                            bg=pal["paper"], fg=pal["ink"],
                            activebackground=pal["seal"], activeforeground="#FFF8EC",
                            bd=1, relief="solid", font=(self.fam_cn, 10))
        self._refresh_menu()

    def _refresh_menu(self):
        m = self.menu
        m.delete(0, "end")
        m.add_command(label="　　设置…", command=self.open_settings)
        m.add_separator()
        m.add_command(label=("　　✓ 锁定窗口尺寸" if self.cfg.get("locked") else "　　　锁定窗口尺寸"),
                      command=self.toggle_lock)
        m.add_command(label=("　　✓ 窗口总在最前" if self.cfg.get("always_on_top") else "　　　窗口总在最前"),
                      command=self.toggle_topmost)
        m.add_command(label="　　恢复默认大小", command=self.reset_size)
        m.add_command(label="　　拉回屏幕", command=self.reset_position)
        m.add_separator()
        m.add_command(label="　　退出", command=self.quit_app)

    def _popup_menu(self, event):
        self._refresh_menu()
        try:
            self.menu.tk_popup(event.x_root, event.y_root)
        finally:
            self.menu.grab_release()

    # ---------------- 绘制 ----------------

    def _on_configure(self, event):
        if event.widget is not self.canvas:
            return
        if (event.width, event.height) == (self.W, self.H):
            return
        self.W, self.H = event.width, event.height
        self.layout()

    # ---- 底色感知的墨色 ----

    def _is_dark_bg(self):
        r, g, b = hex_to_rgb(self.bg_color)
        return (0.299 * r + 0.587 * g + 0.114 * b) / 255.0 < 0.5

    def _ink_tone(self, level="soft"):
        """
        返回在当前底色上可读的墨色。
        底色偏亮时用墨色系，底色转深（例如「入夜」档）时自动换成纸色系，
        这样同一套装饰元素在明暗两种底上都不会消失。
        level: "strong"（正文）/ "soft"（标题）/ "faint"（辅助）
        """
        pal = self.cfg["palette"]
        heavy, light = pal["ink"], pal["paper"]
        # "title" 比 soft 更实一点：顶上那行「目標 · 某月某日」要说清楚在倒数
        # 哪一天，太淡了在小窗口上就跟没有一样。
        ratio = {"strong": 0.0, "title": 0.14, "soft": 0.28,
                 "faint": 0.52}.get(level, 0.28)
        anchor = heavy if not self._is_dark_bg() else light
        other = light if anchor == heavy else heavy
        return mix(anchor, other, ratio)

    def layout(self):
        """整幅重绘（窗口尺寸变化 / 配色切换时调用）。"""
        if getattr(self, "_in_layout", False):
            return
        self._in_layout = True
        try:
            self._layout_impl()
        finally:
            self._in_layout = False

    def _layout_impl(self):
        W = self.W or self.canvas.winfo_width() or self.w
        H = self.H or self.canvas.winfo_height() or self.h
        self.W, self.H = W, H

        pal = self.cfg["palette"]
        if self.remaining is None or self.target is None:
            bg = pal["paper"]
        elif self.zero_mode:
            bg = pal["paper_night"]
        else:
            bg = (self.theme or {}).get("bg") or pal["paper"]
        self.bg_color = bg

        self.canvas.delete("all")
        self._draw_paper(W, H, bg)
        self._draw_frame(W, H)
        self._draw_controls(W, H)
        self._draw_seal(W, H)
        self._draw_head(W, H)
        self.redraw_dynamic()

    def _draw_paper(self, W, H, bg):
        c = self.canvas
        c.create_rectangle(0, 0, W, H, fill=bg, outline="")
        # 宣纸纤维质感：固定随机种子，保证每次重绘纹理一致
        rnd = random.Random(20261001)
        count = max(24, int(W * H / 5200))
        dark = mix(bg, "#000000", 0.10)
        light = mix(bg, "#FFFFFF", 0.22)
        for i in range(count):
            px, py = rnd.uniform(0, W), rnd.uniform(0, H)
            r = rnd.uniform(0.5, 1.8)
            c.create_oval(px - r, py - r, px + r, py + r,
                          fill=(dark if i % 3 else light), outline="")

    def _draw_frame(self, W, H):
        c = self.canvas
        pal = self.cfg["palette"]
        m = max(7, int(min(W, H) * 0.030))
        c.create_rectangle(m, m, W - m, H - m,
                           outline=pal["border"], width=2)
        c.create_rectangle(m + 5, m + 5, W - m - 5, H - m - 5,
                           outline=pal["border_soft"], width=1)
        # 四角回纹角花
        arm = max(10, int(min(W, H) * 0.048))
        for ox, oy, sx, sy in ((m, m, 1, 1), (W - m, m, -1, 1),
                               (m, H - m, 1, -1), (W - m, H - m, -1, -1)):
            c.create_line(ox + sx * 3, oy + sy * arm, ox + sx * 3, oy + sy * 3,
                          ox + sx * arm, oy + sy * 3,
                          fill=pal["border"], width=2)
            c.create_line(ox + sx * 7, oy + sy * (arm - 4), ox + sx * 7, oy + sy * 7,
                          ox + sx * (arm - 4), oy + sy * 7,
                          fill=pal["border_soft"], width=1)

    def _draw_head(self, W, H):
        """顶部目标时刻（写清楚在倒数什么）+ 左下角当前规则名。"""
        pal = self.cfg["palette"]
        m = max(7, int(min(W, H) * 0.030))
        size = self._title_size()
        self.f_title.configure(size=size)

        title = pretty_target(self.target) if self.target else "尚未设定目标时刻"
        # 光一个日期顶在上面，不写清楚它是「目标时刻」，会有人当成今天的日期
        # —— 尤其是「12月25日」这种看着像节日的日子。所以前缀两个字不能省。
        text = ("目標 · " + title) if self.target else title
        # 窄窗口下这行可能顶出两边，逐号往回收到放得下为止
        limit = max(60, W - 2 * m - 24)
        while size > 9 and self.f_title.measure(text) > limit:
            size -= 1
            self.f_title.configure(size=size)
        self.canvas.create_text(W / 2, m + size + 6, text=text,
                                font=self.f_title,
                                fill=self._ink_tone("title"))

        # 左下角：当前配色规则名
        label = (self.theme or {}).get("label") or ""
        if self.zero_mode:
            label = ""
        if label:
            self.f_hint.configure(size=max(8, int(size * 0.78)))
            self.canvas.create_text(m + 16, H - m - 14, text=label, anchor="w",
                                    font=self.f_hint,
                                    fill=self._ink_tone("faint"))

    def _draw_controls(self, W, H):
        """
        右上角三个入口：「設」设置、「—」最小化到任务栏、「✕」退出。

        自动检查发现新版本时，在「設」旁边点一颗朱砂小点。

        为什么还是要自绘而不是用 tk.Button：这个窗口是无边框的
        （overrideredirect），没有系统标题栏可挂按钮；而且整套配色会随
        用户改，自绘才能跟着变。

        整组图元统一挂 "gear" 标签、动手前先删干净：鼠标进出这个区域会被
        反复重画（见 _on_hover），不先删就会一层层叠上去。
        """
        pal = self.cfg["palette"]
        m = max(7, int(min(W, H) * 0.030))
        self.f_gear.configure(size=max(10, min(15, int(H * 0.058))))
        cy = m + 19
        # 间距跟着窗口尺寸走：窗口缩到 300 宽时挤不下三个 24px 的间隔
        step = max(CTRL_STEP_MIN, int(min(W, H) * 0.085))
        # 从右往左排：关闭在最外侧、最小化其次、设置在最里面。
        # 「設」留在原来习惯的位置附近，老用户不会找不到。
        self._ctl_pos = {
            "close": (W - m - 18, cy),
            "min": (W - m - 18 - step, cy),
            "gear": (W - m - 18 - step * 2, cy),
        }
        self.canvas.delete("gear")
        faint = self._ink_tone("faint")
        for name, glyph in (("gear", "設"), ("min", "—"), ("close", "✕")):
            x, y = self._ctl_pos[name]
            self.canvas.create_text(
                x, y, text=glyph, font=self.f_gear, tags="gear",
                fill=pal["seal"] if self._ctl_hover == name else faint)
        if self.new_version:
            # 只点一颗小点：不写字、不弹窗。想升级的人自然会去点「設」，
            # 不想升级就一直是一颗点，不打扰。
            gx, gy = self._ctl_pos["gear"]
            r = max(2.5, min(W, H) * 0.011)
            cx, cy2 = gx + r * 3.0, gy - r * 3.0
            self.canvas.create_oval(cx - r, cy2 - r, cx + r, cy2 + r,
                                    fill=pal["seal"], outline="", tags="gear")

    def _ctl_at(self, x, y):
        """
        落在哪个右上角按钮上；没踩着返回 ""。

        取「最近的那一枚」而不是字典里第一个碰上的：三个按钮里最外侧是「✕」，
        万一间距被改小到命中框搭界，先到先得会让「关闭」抢走本该给「最小化」的点。
        取最近至少保证点谁算谁。
        """
        best, best_d = "", None
        for name, (bx, by) in (self._ctl_pos or {}).items():
            dx, dy = x - bx, y - by
            if abs(dx) <= CTRL_HIT and abs(dy) <= CTRL_HIT:
                d = dx * dx + dy * dy
                if best_d is None or d < best_d:
                    best, best_d = name, d
        return best

    def _draw_seal(self, W, H):
        """右下角朱砂印。"""
        pal = self.cfg["palette"]
        m = max(7, int(min(W, H) * 0.030))
        s = max(26, min(46, int(min(W, H) * 0.145)))
        x1, y1 = W - m - 14 - s, H - m - 14 - s
        self.canvas.create_rectangle(x1, y1, x1 + s, y1 + s,
                                     fill=pal["seal"], outline="")
        self.canvas.create_rectangle(x1 + 3, y1 + 3, x1 + s - 3, y1 + s - 3,
                                     outline=mix(pal["seal"], "#FFFFFF", 0.35), width=1)
        self.f_seal.configure(size=max(11, int(s * 0.46)))
        # 印文固定用亮色（朱红印面之上），不随底色反转
        self.canvas.create_text(x1 + s / 2, y1 + s / 2, text="時",
                                font=self.f_seal, fill=mix(pal["paper"], "#FFFFFF", 0.12))

    # ---- 动态部分（每次刷新重建，物品数很少，开销可忽略） ----

    def redraw_dynamic(self):
        self.canvas.delete("dyn")
        if self.target is None:
            self._draw_error()
        elif self.zero_mode:
            self._draw_zero()
        else:
            self._draw_digits()

    def _title_size(self):
        """
        顶部「目標 · 某月某日」那行字的字号。

        比原先大一号（原来上限 16、下限 9）：窗口拉到最小时那行只有 9px，
        用户根本看不清倒计时到哪一天，而这行恰恰是「这个挂件在为什么事
        倒数」的唯一说明。小窗口下尤其不该缩到看不清。
        """
        return max(11, min(22, int(self.H * 0.085)))

    def _head_bottom(self, m=None):
        """标题区下沿：数字从这里往下排。与 _draw_head 用同一套算法。"""
        m = max(7, int(min(self.W, self.H) * 0.030)) if m is None else m
        return int(m + self._title_size() * 1.6 + 10)

    def _region(self):
        """
        数字可用区域 (left, top, right, bottom)。

        四周留白压得比较紧（左右各 m+16、底部 m+16，原来是 30 / 26）：
        这个挂件的全部意义就是那一串数字，留白多一寸字就白小一号。
        用户把窗口拉到最小时抱怨的正是「字太小」，所以能给的空间都给数字。
        """
        m = max(7, int(min(self.W, self.H) * 0.030))
        return (m + 16, self._head_bottom(m), self.W - m - 16, self.H - m - 16)

    # ---- 字号拟合：比例估算 + 缓存，避免逐号试错 ----

    def _apply_num_size(self, size):
        self.f_num.configure(size=size)
        self.f_unit.configure(size=max(8, int(size * 0.36)))

    def _ensure_num_size(self, size):
        unit_size = max(8, int(size * 0.36))
        if int(self.f_num.cget("size")) != size or int(self.f_unit.cget("size")) != unit_size:
            self._apply_num_size(size)

    def _num_spacing(self, size):
        """
        数字与单位之间的间隙、以及两组之间的间隙。

        比例从 0.26 / 0.42 压到 0.18 / 0.30：四组数字之间的空档原本吃掉近
        三成宽度，收窄之后同一个窗口能放大约一成的字号。这正是「窗口拉小
        时字太小」最直接的补偿，而且不动任何布局结构。
        """
        return max(4, int(size * 0.18)), max(7, int(size * 0.30))

    def _block_width(self, pairs, size, gap, grp):
        total = 0
        for num, unit, _ in pairs:
            total += self.f_num.measure(num) + gap + self.f_unit.measure(unit)
        return total + grp * (len(pairs) - 1)

    def _fit_num_size(self, pairs, avail_w, avail_h):
        """
        按比例估算字号，再做几次几何收敛。

        注意：在 Tk 中切换字体约需 8ms，若从大字号逐个往下试，
        一轮排版会累积到数百毫秒；比例估算把字体切换次数压到 2~5 次。
        """
        probe = 100
        self._apply_num_size(probe)
        w0 = self._block_width(pairs, probe, *self._num_spacing(probe))
        h0 = max(1, self.f_num.metrics("linespace"))
        if w0 <= 0:
            return probe

        size = max(MIN_NUM_SIZE, min(400,
                                     int(probe * min(avail_w / w0, avail_h / h0))))
        for _ in range(5):
            self._apply_num_size(size)
            gap, grp = self._num_spacing(size)
            w = self._block_width(pairs, size, gap, grp)
            h = self.f_num.metrics("linespace")
            if w <= avail_w and h <= avail_h:
                break
            nxt = max(MIN_NUM_SIZE,
                      int(size * min(avail_w / max(1, w), avail_h / max(1, h)) * 0.97))
            if nxt >= size:
                nxt = size - 1
            if nxt < MIN_NUM_SIZE:
                size = MIN_NUM_SIZE
                break
            size = nxt

        self._apply_num_size(size)
        return size

    def _fit_zero_size(self, text, avail_w, avail_h):
        probe = 100
        self.f_zero.configure(size=probe)
        w0 = max(1, self.f_zero.measure(text))
        h0 = max(1, self.f_zero.metrics("linespace"))

        size = max(10, min(400, int(probe * min(avail_w / w0, avail_h / h0))))
        for _ in range(5):
            self.f_zero.configure(size=size)
            w = self.f_zero.measure(text)
            h = self.f_zero.metrics("linespace")
            if w <= avail_w and h <= avail_h:
                break
            nxt = max(10, int(size * min(avail_w / max(1, w), avail_h / max(1, h)) * 0.97))
            if nxt >= size:
                nxt = size - 1
            if nxt < 10:
                size = 10
                break
            size = nxt

        if int(self.f_zero.cget("size")) != size:
            self.f_zero.configure(size=size)
        return size

    def _draw_digits(self):
        c = self.canvas
        pal = self.cfg["palette"]
        rem = max(0.0, self.remaining or 0.0)
        days = int(rem // 86400)
        hours = int(rem % 86400 // 3600)
        mins = int(rem % 3600 // 60)
        secs = int(rem % 60)

        pairs = [(str(days), "日", False), ("%02d" % hours, "時", False),
                 ("%02d" % mins, "分", False), ("%02d" % secs, "秒", True)]

        left, top, right, bottom = self._region()
        avail_w = max(60, right - left)
        avail_h = max(30, bottom - top)

        # 字号只取决于「可用空间 + 各数字的位数」。位数在绝大多数秒内不变，
        # 因此缓存命中后每秒刷新不必再做任何字号度量。
        key = (avail_w // 4, avail_h // 4, tuple(len(n) for n, _, _ in pairs))
        if key != self._digits_key:
            self._digits_key = key
            self._digits_size = self._fit_num_size(pairs, avail_w, avail_h)
        size = self._digits_size
        self._ensure_num_size(size)

        gap, grp = self._num_spacing(size)
        total = self._block_width(pairs, size, gap, grp)

        fg = (self.theme or {}).get("fg") or pal["default_fg"]
        fg_unit = mix(fg, self.bg_color, 0.28)
        cy = (top + bottom) / 2.0

        x = left + max(0.0, (avail_w - total) / 2.0)
        for num, unit, is_sec in pairs:
            nw = self.f_num.measure(num)
            uw = self.f_unit.measure(unit)
            c.create_text(x + nw / 2.0, cy, text=num, font=self.f_num,
                          fill=fg, tags="dyn")
            c.create_text(x + nw + gap, cy + size * 0.29, text=unit, anchor="w",
                          font=self.f_unit, fill=fg_unit, tags="dyn")
            x += nw + gap + uw + grp

    def _draw_zero(self):
        c = self.canvas
        zone_color = self.cfg.get("zero_color", "#B03A2E")
        alt = self.cfg.get("zero_color_alt", "#D9A13B")
        color = alt if self.blink else zone_color
        text = self.cfg.get("zero_text", "時辰已到")

        left, top, right, bottom = self._region()
        # 留出四周呼吸感，避免字形顶到边框
        avail_w = max(60, (right - left) * 0.84)
        avail_h = max(30, (bottom - top) * 0.80)

        # 归零提示文字固定，同样走缓存，闪烁刷新时不再做字号度量
        key = (avail_w // 4, avail_h // 4, text)
        if key != self._zero_key:
            self._zero_key = key
            self._zero_size = self._fit_zero_size(text, avail_w, avail_h)
        if int(self.f_zero.cget("size")) != self._zero_size:
            self.f_zero.configure(size=self._zero_size)

        c.create_text((left + right) / 2.0, (top + bottom) / 2.0, text=text,
                      font=self.f_zero, fill=color, tags="dyn")

    def _draw_error(self):
        c = self.canvas
        pal = self.cfg["palette"]
        left, top, right, bottom = self._region()
        msg = self.parse_err or "时间格式无法识别"
        self.f_zero.configure(size=max(14, min(30, int((right - left) / max(6, len(msg)) * 1.7))))
        c.create_text((left + right) / 2.0, (top + bottom) / 2.0, text="⚠ " + msg,
                      font=self.f_zero, fill=pal["seal"], tags="dyn")

    # ---------------- 计时核心 ----------------

    def tick(self):
        """
        每帧只做极轻量的工作；不使用死循环，调度点对齐到下一个整秒，
        因此空闲时 CPU 占用约等于 0。
        """
        now = datetime.datetime.now()

        # 顺带看一眼有没有第二个实例在喊「现身」（一次注册表读，开销可忽略）
        if reg_store_read("wake", None) is not None:
            self._consume_wake()

        # 传书巡检。每 30 秒才真跑一次 —— 中间那些秒只是一次减法比较，
        # 在纳秒量级，实测不出与改造前的差别。
        # 首次 tick 必然触发，相当于开机时补做一次「错过的提醒」。
        clock = now.timestamp()
        if clock - self._last_notify_check >= NOTIFY_CHECK_SEC:
            self._last_notify_check = clock
            self.notify_tick(now)

        # 自动检查更新：启动后先静置 60 秒，之后每 6 小时醒一次。
        # 醒来也不一定真查 —— 要不要发网络请求，得看「距上次查通满没满 7 天」，
        # 而那只是一次注册表读。绝大多数巡检到这里就是一次时间戳比较。
        if clock >= self._update_scan_at:
            self._update_scan_at = clock + UPDATE_AUTO_SCAN_SEC
            try:
                self.auto_update_scan()
            except Exception as exc:          # noqa: BLE001
                # 这一段绝不允许拖垮 tick —— tick 一断，倒计时就彻底不动了。
                # 为了一个「顺带检查更新」把主功能赔进去，那是本末倒置。
                note_scan_error(exc)

        if self.target is None:
            stamp = ("err", self.parse_err)
            theme = None
            need_redraw = stamp != self._last_text
            idle = False
        else:
            self.remaining = (self.target - now).total_seconds()
            self.zero_mode = self.remaining <= 0
            idle = self.zero_mode
            if idle:
                self.blink = not self.blink
                stamp = ("zero", self.blink)
                need_redraw = True
            else:
                stamp = ("run", int(self.remaining))
                need_redraw = stamp != self._last_text
            theme = None if idle else pick_theme(self.remaining, self.cfg)

        self._last_text = stamp

        if theme != self.theme:
            self.theme = theme
            self.layout()
        elif need_redraw:
            self.redraw_dynamic()

        if self.target is None:
            delay = 1000
        elif idle:
            delay = TICK_IDLE_MS
        else:
            delay = max(30, 1000 - now.microsecond // 1000)
        self.root.after(delay, self.tick)

    # ---------------- 在线升级 · 自动部分 ----------------

    def _on_tk_error(self, exc_type, exc_value, exc_tb):
        """
        Tk 回调（包括 tick）里没接住的异常。

        没有它的话，任何一次意外都会让 after 链断掉 —— 倒计时从此不再刷新，
        而用户看不见、我们也查不到。
        """
        log_problem("Tk 回调", exc_type, exc_value, exc_tb)

    def _note_run_ok(self):
        """
        启动满 60 秒后走这里：给 .old 的保留计数 +1，攒够次数才真的删。

        刻意放在定时器里而不是启动路径上：一是要把「起不来」和「起来了」
        分开 —— 崩在启动阶段的版本不该拿到这一笔；二是注册表写和可能的
        重试都不该挤在启动那几百毫秒里。
        """
        try:
            note_successful_run()
        except Exception as exc:             # noqa: BLE001
            note_scan_error(exc)             # 不留痕的话，出事就只能靠猜

    def set_new_version(self, ver):
        """
        记下「线上有新版本」，并同步右上角那颗小红点。

        传空、或传一个不比本机新的版本号，就是把红点灭掉 ——
        手动点到「已是最新版本」之后走的就是这条路。
        """
        known = str(ver or "")
        if not update_available(known):
            known = ""
        if known == self.new_version:
            return
        self.new_version = known
        try:
            self._draw_controls(self.W, self.H)
        except Exception:                    # noqa: BLE001
            pass

    def auto_update_scan(self):
        """
        自动检查的巡检：先判断该不该查，该查才起后台线程。

        三条底线（比这个功能本身重要）：
          · 绝不弹窗、绝不在界面上写任何失败文字；
          · 绝不阻塞界面线程 —— 真正的查询在后台线程里跑；
          · 出任何意外都就地吞掉，倒计时该怎么走还怎么走。
        """
        if not self.cfg.get("auto_update_check", True):
            return
        if time.time() - last_auto_check_ts() < UPDATE_CHECK_MIN_GAP:
            return                           # 7 天内查过，读到这儿就收工

        def worker():
            try:
                info, err = fetch_update_info()
            except Exception as exc:         # noqa: BLE001
                note_scan_error(exc)
                return
            if err or not info:
                # 没查通（断网、通道抽风）不算异常，但值得留一行痕：
                # 用户说「一直没提示更新」时，第一件事就是来看这里。
                note_scan_error(RuntimeError("查询没通：%s"
                                             % (err or "没有返回内容")))
                return
            ver = str(info.get("version") or "")
            try:
                note_auto_check(ver)
            except Exception as exc:         # noqa: BLE001
                note_scan_error(exc)
                return
            if not update_available(ver):
                return                       # 已是最新：连界面都不用碰
            try:
                self.root.after(0, lambda v=ver: self.set_new_version(v))
            except Exception as exc:         # noqa: BLE001
                note_scan_error(exc)

        import threading
        try:
            threading.Thread(target=worker, daemon=True).start()
        except Exception:                    # noqa: BLE001
            pass

    # ---------------- 窗口拖拽 / 缩放 ----------------

    def _geometry(self):
        return self.x, self.y, self.w, self.h

    def _apply_geometry(self, x, y, w, h):
        self.x, self.y, self.w, self.h = int(x), int(y), int(w), int(h)
        set_geometry(self.root, self.w, self.h, self.x, self.y)
        self.W, self.H = self.w, self.h

    def hit_test(self, px, py):
        if self.cfg.get("locked"):
            return ""
        m = RESIZE_MARGIN
        left, right = px <= m, px >= self.W - m
        top, bottom = py <= m, py >= self.H - m
        if top and left:
            return "nw"
        if top and right:
            return "ne"
        if bottom and left:
            return "sw"
        if bottom and right:
            return "se"
        if top:
            return "n"
        if bottom:
            return "s"
        if left:
            return "w"
        if right:
            return "e"
        return ""

    def _on_hover(self, event):
        if self._dragging:
            return
        name = self._ctl_at(event.x, event.y)
        if name != self._ctl_hover:
            self._ctl_hover = name
            self._draw_controls(self.W, self.H)

        if name:
            self.canvas.configure(cursor="hand2")
            return

        mode = self.hit_test(event.x, event.y)
        cursor = {"nw": "size_nw_se", "se": "size_nw_se",
                  "ne": "size_ne_sw", "sw": "size_ne_sw",
                  "n": "size_ns", "s": "size_ns",
                  "w": "size_we", "e": "size_we"}.get(mode, "fleur")
        self.canvas.configure(cursor=cursor)

    def _on_press(self, event):
        name = self._ctl_at(event.x, event.y)
        if name == "gear":
            self.open_settings()
            return
        if name == "min":
            self.minimize_app()
            return
        if name == "close":
            self.quit_app()
            return

        mode = self.hit_test(event.x, event.y)
        if not mode and self.cfg.get("locked"):
            mode = ""            # 锁定态下仅允许移动
        self._drag_mode = mode if mode else "move"
        self._dragging = True
        self._press_pt = (event.x_root, event.y_root)
        self._press_geo = self._geometry()

    def _on_drag(self, event):
        if not self._dragging:
            return
        dx = event.x_root - self._press_pt[0]
        dy = event.y_root - self._press_pt[1]
        x, y, w, h = self._press_geo
        mode = self._drag_mode

        if mode == "move":
            # 拖动时也受约束：不让窗口被推出桌面，从源头杜绝「存下越界坐标」
            nx, ny, _ = self.clamp_position(x + dx, y + dy, w, h)
            self._apply_geometry(nx, ny, w, h)
            return

        if "e" in mode:
            w = max(MIN_W, w + dx)
        if "s" in mode:
            h = max(MIN_H, h + dy)
        if "w" in mode:
            new_w = max(MIN_W, w - dx)
            x = x + (w - new_w)
            w = new_w
        if "n" in mode:
            new_h = max(MIN_H, h - dy)
            y = y + (h - new_h)
            h = new_h
        self._apply_geometry(x, y, w, h)

    def _on_release(self, event):
        if not self._dragging:
            return
        self._dragging = False
        if self._drag_mode != "move":
            self.W, self.H = self.w, self.h
            self.layout()
        self._remember_geometry()

    def _remember_geometry(self):
        win = self.cfg.setdefault("window", {})
        snapshot = {"x": self.x, "y": self.y, "w": self.w, "h": self.h}
        # 位置未变化时不写盘，避免拖动过程中频繁 IO
        if all(win.get(k) == v for k, v in snapshot.items()):
            return
        win.update(snapshot)
        save_config(self.cfg)

    def reset_size(self):
        self._apply_geometry(self.x, self.y, 620, 300)
        self.W, self.H = self.w, self.h
        self.layout()
        self._remember_geometry()

    def resize_to(self, w, h):
        """
        按给定的宽高改窗口尺寸（设置面板里那个「应用」走这里）。
        返回错误文本；空串 = 改好了。

        为什么要有这个口子：窗口大小一直是靠拖边缘调的，可拖出来是多大
        没有任何地方写着 —— 想让几台机器调成一样、或者照着某个尺寸复原，
        只能凭手感来回试。给一个能看见、能填准的地方，比再拖十次有用。
        """
        if self.cfg.get("locked"):
            return "窗口尺寸已锁定：先取消「锁定窗口尺寸」再改"
        try:
            w, h = int(float(w)), int(float(h))
        except (TypeError, ValueError):
            return "尺寸要填数字"
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        # 上下都夹住：太小会看不清字（MIN_W/MIN_H），太大就顶出屏幕了
        w = max(MIN_W, min(w, sw))
        h = max(MIN_H, min(h, sh))
        x, y, _ = self.clamp_position(self.x, self.y, w, h)
        self._apply_geometry(x, y, w, h)
        self.layout()
        self._remember_geometry()
        return ""

    def reset_position(self):
        """把窗口挪回默认位置——万一它跑到屏幕外，靠这个救回来。"""
        x, y = self.default_position()
        self._apply_geometry(x, y, self.w, self.h)
        self.root.deiconify()
        self.root.lift()
        self._restore_chrome()
        self._remember_geometry()

    def minimize_app(self):
        """
        最小化到任务栏（右上角「—」）。

        无边框窗口（overrideredirect）直接 iconify 在 Windows 上会
        「窗口不见了、任务栏里也没有」—— 等于把程序弄丢，用户只好像
        重启电脑那样找它。所以先临时把系统边框交还回去，
        任务栏才肯接管它；从任务栏恢复时再由 _restore_chrome 收回边框。

        恢复这条链路有两道保险：<Map> 事件，以及用户重新双击 exe 时的
        唤醒信号（_consume_wake 会走到 reset_position，那里也会收回边框）。
        """
        try:
            self.root.overrideredirect(False)
            self.root.iconify()
        except tk.TclError:
            pass

    def _restore_chrome(self):
        """
        把系统边框收回去、尺寸位置摆回原位。

        只在「边框确实被交还给了系统」时才动手，所以重复调用是安全的。
        """
        try:
            if self.root.state() != "normal" or chrome_hidden(self.root):
                return
            self.root.overrideredirect(True)
            self.root.attributes("-topmost", bool(self.cfg.get("always_on_top", True)))
            self.root.update_idletasks()
            # 交还边框时系统会按标题栏高度改窗口矩形，收回来之后要摆回原位
            set_geometry(self.root, self.w, self.h, self.x, self.y)
            self.layout()
        except tk.TclError:
            pass

    def _on_root_map(self, event=None):
        """窗口从任务栏恢复（或重新拿到焦点）时，把自绘边框还原。"""
        if event is not None and getattr(event, "widget", None) is not self.root:
            return
        self._restore_chrome()

    def _consume_wake(self):
        """另一个实例被启动了：用户想看见窗口，那就把自己挪回可见处。"""
        clear_wake_file()
        self.reset_position()

    def toggle_lock(self):
        self.cfg["locked"] = not self.cfg.get("locked", False)
        save_config(self.cfg)
        self._refresh_menu()

    def toggle_topmost(self):
        self.cfg["always_on_top"] = not self.cfg.get("always_on_top", True)
        self.root.attributes("-topmost", bool(self.cfg["always_on_top"]))
        save_config(self.cfg)
        self._refresh_menu()

    def quit_app(self):
        self._remember_geometry()
        self.root.destroy()

    # ---------------- 鸿雁传书（邮件通知）----------------
    #
    # 分工很明确：主进程只判断「该不该寄」并派生一个短命进程，
    # 真正的网络收发全在那个进程里完成。所以无论发信成功还是卡住，
    # 主进程的内存和响应速度都不受影响。

    def notify_configured(self):
        """四处都齐了才谈得上寄信；缺一样就静默跳过，不打扰。"""
        nd = self.cfg.get("notify") or {}
        if not nd.get("enabled"):
            return False
        if not (nd.get("user") or "").strip():
            return False
        if not (nd.get("host") or "").strip():
            return False
        if not (self.secret.get("smtp_password") or "").strip():
            return False
        return True

    def notify_recipient(self):
        nd = self.cfg.get("notify") or {}
        return (nd.get("to") or "").strip() or (nd.get("user") or "").strip()

    def notify_signature(self):
        """
        本机抬头。留空 = 不加抬头，主题沿用「【倒计时】…」的老样子。

        新版第一次运行会由 load_config 种入计算机名，所以正常情况下这里
        拿到的是「DESKTOP-XXXX」这类名字，用户改过就是「书房台机」。
        """
        nd = self.cfg.get("notify") or {}
        return sanitize_signature(nd.get("signature"))

    def mail_subject(self, tail):
        """
        按本机抬头拼主题 —— 正式寄信和试寄共用这一个来源。

        为什么要抽出来：早先试寄那条路自己硬编码了「【倒计时】试寄一封」，
        结果抬头加好后，正式信带抬头、试寄不带 —— 而试寄恰恰是用户
        唯一能先看到效果的地方，等于白改。同一件事有两个来源就迟早分叉。
        """
        sign = self.notify_signature()
        if sign:
            return "【%s】倒计时 · %s" % (sign, tail)
        return "【倒计时】%s" % tail            # 没设抬头 = 与旧版逐字一致

    def mail_footer(self):
        """落款。有抬头就冠在最前，收件箱列表里一眼看出是哪台机器寄的。"""
        sign = self.notify_signature()
        tail = ("%s · 古风倒计时自动传书" % sign) if sign \
            else "古风倒计时 · 自动传书"
        return ["", "—— %s" % tail,
                "这封信由桌面上的小工具自动寄出，不必回复。"]

    def notify_tick(self, now):
        """巡检一次：先把上次的结果收回来，再判断这次该不该寄。"""
        self.collect_notify_result()

        if not self.notify_configured() or self.target is None:
            return

        st = self.notify_state
        key = self.target.strftime("%Y-%m-%dT%H:%M:%S")
        if st.get("target_key") != key:
            # 换了目标时刻 = 换了一件事。旧的发送履历必须作废，
            # 否则新目标会被旧记录挡住，永远不通知。
            st["target_key"] = key
            st["history"] = []
            save_notify_state(st)

        remaining = (self.target - now).total_seconds()
        # 顺手校准：邮件正文里的剩余时间取自这里。
        # tick 里原本的赋值发生在本函数之后，不校准就会用上一秒的旧值。
        self.remaining = remaining
        rules = self.cfg["notify"].get("rules") or []

        due = []
        for idx, rule in enumerate(rules):
            if not rule.get("enabled", True):
                continue
            try:
                threshold = float(rule.get("days") or 0.0) * 86400.0
            except (TypeError, ValueError):
                continue
            if remaining > threshold:
                continue

            # 注意：超时与重试一律用真实时钟（time.time）比较。
            # 履历里的 at_ts / next_try 就是按真实时钟写的，
            # 混用两套计时基准会在时间被改动时误判。
            rec = self.find_notify_record(idx)
            if rec is None:
                due.append((threshold, idx, rule, "首次"))
            elif rec.get("status") == "failed" \
                    and int(rec.get("tries", 1)) < NOTIFY_MAX_RETRY \
                    and time.time() >= float(rec.get("next_try", 0)):
                due.append((threshold, idx, rule, "重试"))
            elif rec.get("status") == "sending" \
                    and time.time() - float(rec.get("at_ts", 0)) > NOTIFY_SENDING_TIMEOUT:
                # 发信进程没回音（被杀掉、或系统休眠掐断了它）。
                # 同样要退避，否则下一轮巡检立刻重发，成了连击。
                rec["status"] = "failed"
                rec["error"] = "发信进程没有回音，稍后会再试"
                rec["next_try"] = time.time() + NOTIFY_RETRY_SEC
                save_notify_state(st)

        if not due:
            return

        # 只寄最紧迫的那一封。开机时若已跨过多档（例如关机三天后才开机），
        # 三封一起补发就成了骚扰 —— 一封信讲清现状就够了。
        due.sort(key=lambda item: item[0])
        _, idx, rule, reason = due[0]
        self.dispatch_notify(idx, rule, reason)

        # 其余更宽松的档位记为「已错过」，不再补发
        for _, other_idx, other_rule, other_reason in due[1:]:
            if other_reason != "首次":
                continue
            self.upsert_notify_record(other_idx, {
                "days": other_rule.get("days"),
                "status": "skipped",
                "error": "",
                "at": _stamp(),
            })
        save_notify_state(st)

    def find_notify_record(self, idx):
        for rec in self.notify_state.get("history", []):
            if rec.get("rule") == idx:
                return rec
        return None

    def upsert_notify_record(self, idx, data):
        hist = self.notify_state.setdefault("history", [])
        for rec in hist:
            if rec.get("rule") == idx:
                rec.update(data)
                return rec
        rec = {"rule": idx}
        rec.update(data)
        hist.append(rec)
        return rec

    def compose_notify_mail(self, rule, reason):
        left = max(0.0, self.remaining or 0.0)
        human = _human_delta(left) if left > 0 else "已到时刻"
        label = rule.get("label") or _rule_label(rule.get("days"))
        clock_desc = self.target.strftime("%Y-%m-%d %H:%M") if self.target else "—"
        target_desc = pretty_target(self.target) if self.target else "未设定"

        # 抬头放在主题最前面：收件箱的列表会把长标题截断，
        # 而「哪台机器寄的」正是最不该被截掉的信息；「倒计时」反倒可以靠后。
        sign = self.notify_signature()
        tail = label if left <= 0 else "还剩 %s（%s）" % (human, label)
        subject = self.mail_subject(tail)
        if reason == "重试":
            subject = "[重发] " + subject

        lines = ["你设下的时刻已经到了。"] if left <= 0 \
            else ["距你设下的时刻，还有 %s。" % human]
        lines += [
            "",
            "目标时刻　%s" % clock_desc,
            "　对应　　%s" % target_desc,
            "当前剩余　%s" % human,
            "提醒档位　%s" % label,
        ]
        if sign:
            lines.append("寄出机器　%s" % sign)
        if reason == "重试":
            lines.append("（这一封是重发，前一次没能寄出去）")
        lines += self.mail_footer()
        body = "\n".join(lines)
        if len(body.encode("utf-8")) > NOTIFY_BODY_LIMIT:
            body = body.encode("utf-8")[:NOTIFY_BODY_LIMIT].decode("utf-8", "ignore")
        return subject, body

    def _spawn_mailer(self, token, subject, body, test_mode=False):
        """写任务文件 + 派生发信进程。返回 (是否成功, 失败说明)。"""
        import subprocess      # 延迟导入：只有真要寄信时才付这份成本

        nd = self.cfg.get("notify") or {}
        task = build_notify_task(nd, self.secret, token, subject, body,
                                 self.notify_recipient(), self.notify_signature())

        ok, err = reg_store_write("notify_task", task)
        if not ok:
            return False, "任务写不进注册表：%s" % err

        # 两条启动路径，见 mailer_target()：平时用解释器跑 .pyw；
        # 打包后若 .pyw 没有好的关联程序，就让 exe 自己兼任发信脚本。
        target, prefix = mailer_target()
        if not target:
            reg_store_delete("notify_task")       # 任务里含授权码，别留在注册表
            return False, "找不到发信脚本 %s" % MAILER_FILE
        argv = [target] + prefix
        if not prefix:
            argv = [pythonw_executable(), target]
        if test_mode:
            argv.append("test")
        flags = 0x08000000 if os.name == "nt" else 0      # CREATE_NO_WINDOW

        # 用环境变量把「数据仓在哪」明确告诉发信进程。
        #
        # 不能指望它自己猜：注册表键名带演练后缀（ ANCIENT_COUNTDOWN_HOME
        # 触发的隔离通道），发信进程必须读写同一个键才能交回结果。
        # HOME 继续传：发信崩溃日志、迁移逻辑还认它。
        env = dict(os.environ)
        env["ANCIENT_COUNTDOWN_HOME"] = DATA_DIR
        env["ANCIENT_COUNTDOWN_REGKEY"] = reg_store_key()
        try:
            subprocess.Popen(
                argv,
                cwd=DATA_DIR,
                creationflags=flags,
                close_fds=True,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                env=env,
            )
        except Exception as exc:                          # noqa: BLE001
            reg_store_delete("notify_task")               # 里面含授权码，别留在注册表
            return False, "发信进程起不来：%s" % exc
        return True, ""

    def dispatch_notify(self, idx, rule, reason):
        subject, body = self.compose_notify_mail(rule, reason)
        token = "%s-%d-%d" % (_stamp("%H%M%S"), idx, random.randint(100, 999))

        ok, err = self._spawn_mailer(token, subject, body)
        if not ok:
            self.set_notify_note("传书失败：" + err)
            return False

        prev = self.find_notify_record(idx) or {}
        self.upsert_notify_record(idx, {
            "days": rule.get("days"),
            "status": "sending",
            "token": token,
            "at": _stamp(),
            "at_ts": time.time(),
            "reason": reason,
            "tries": int(prev.get("tries", 0)) + 1,
            "error": "",
        })
        save_notify_state(self.notify_state)
        self.set_notify_note("正在传书…")
        return True

    def collect_notify_result(self):
        """取回发信进程留下的结果。没有结果时只花一次注册表读。"""
        data = reg_store_read("notify_result", None)
        if data is None:
            return
        reg_store_delete("notify_result")
        if not isinstance(data, dict):
            return

        token = data.get("token")
        rec = None
        for item in self.notify_state.get("history", []):
            if item.get("token") == token:
                rec = item
                break
        if rec is None:
            return

        if data.get("ok"):
            rec["status"] = "sent"
            rec["error"] = ""
            rec["sent_at"] = _stamp()
            self.set_notify_note("传书已送达")
        else:
            message = (data.get("error") or "未知错误").strip()
            rec["status"] = "failed"
            rec["error"] = message
            rec["next_try"] = time.time() + NOTIFY_RETRY_SEC
            tries = int(rec.get("tries", 1))
            if tries >= NOTIFY_MAX_RETRY:
                self.set_notify_note("传书失败（已试 %d 次）：%s" % (tries, message[:48]))
            else:
                self.set_notify_note("传书失败，稍后重试：%s" % message[:48])
        save_notify_state(self.notify_state)

    def set_notify_note(self, text):
        self._notify_note = text
        self._notify_note_at = time.time()

    def send_test_mail(self):
        """试寄一封：不写履历，纯验证配置。返回 (token, None) 或 (None, 错误)。"""
        nd = self.cfg.get("notify") or {}
        sender = (nd.get("user") or "").strip()
        if not sender:
            return None, "请先填写发件邮箱"
        if not looks_like_mail(sender):
            return None, "发件邮箱「%s」看着不完整，是不是少写了一个点" % sender
        if not (self.secret.get("smtp_password") or "").strip():
            return None, "请先填写授权码"
        if not (nd.get("host") or "").strip():
            return None, "请先选择邮箱服务商"
        rcpt = self.notify_recipient()
        if not looks_like_mail(rcpt):
            return None, "收件邮箱「%s」看着不完整，是不是少写了一个点" % rcpt

        left = max(0.0, self.remaining or 0.0)
        sign = self.notify_signature()
        lines = [
            "这是一封试寄的信，用来确认邮箱设置能不能正常寄出。",
            "",
            "如果收到了，就说明配置没问题。",
            "",
            "顺带报一下当前状态：",
            "目标时刻　%s" % (self.target.strftime("%Y-%m-%d %H:%M") if self.target else "未设定"),
            "当前剩余　%s" % (_human_delta(left) if left > 0 else "已到时刻"),
        ]
        if sign:
            lines.append("寄出机器　%s" % sign)
        # 落款、主题都走公共拼装 —— 试寄必须和正式信长得一模一样，
        # 否则「试寄看着没问题、正式寄来却不同」比不带抬头更糟。
        lines += self.mail_footer()
        body = "\n".join(lines)
        if len(body.encode("utf-8")) > NOTIFY_BODY_LIMIT:
            body = body.encode("utf-8")[:NOTIFY_BODY_LIMIT].decode("utf-8", "ignore")
        token = "test-%s" % _stamp("%H%M%S")
        ok, err = self._spawn_mailer(token, self.mail_subject("试寄一封"), body,
                                     test_mode=True)
        if not ok:
            return None, err
        return token, None

    def show_notify_log(self):
        """摊开传书履历 —— 免得「到底寄出去没有」只能靠猜。"""
        existing = getattr(self, "_log_win", None)
        if existing is not None:
            try:
                existing.lift()
                existing.deiconify()
                return
            except tk.TclError:
                self._log_win = None

        pal = self.cfg["palette"]
        nd = self.cfg.get("notify") or {}
        win = tk.Toplevel(self.root)
        self._log_win = win
        win.overrideredirect(True)
        win.configure(bg=pal["border"])
        win.attributes("-topmost", True)

        body = tk.Frame(win, bg=pal["paper"])
        body.pack(fill="both", expand=True, padx=3, pady=3)

        head = tk.Frame(body, bg=pal["ink"], height=34)
        head.pack(fill="x")
        head.pack_propagate(False)
        tk.Label(head, text="　传 书 记 录", bg=pal["ink"], fg=pal["paper"],
                 font=(self.fam_cn, 11, "bold")).pack(side="left", padx=10)
        closer = tk.Label(head, text="✕", bg=pal["ink"], fg=pal["border_soft"],
                          font=("Segoe UI", 10), cursor="hand2", padx=12)
        closer.pack(side="right", fill="y")

        def shut(event=None):
            self._log_win = None
            try:
                win.destroy()
            except tk.TclError:
                pass

        closer.bind("<Button-1>", shut)
        win.bind("<Escape>", shut)

        wrap = tk.Frame(body, bg=pal["paper"])
        wrap.pack(fill="both", expand=True, padx=18, pady=14)

        if not nd.get("enabled"):
            summary, tint = "传书未开启", pal["ink_soft"]
        elif not self.notify_configured():
            summary, tint = "传书已开启，但配置还缺东西", pal["seal"]
        else:
            summary, tint = "传书已开启　→　%s" % self.notify_recipient(), "#4F7A52"
        tk.Label(wrap, text=summary, bg=pal["paper"], fg=tint,
                 font=(self.fam_cn, 10, "bold"), anchor="w").pack(fill="x")

        if self._notify_note:
            tk.Label(wrap, text=self._notify_note, bg=pal["paper"], fg=pal["ink_soft"],
                     font=(self.fam_cn, 9), anchor="w", wraplength=380,
                     justify="left").pack(fill="x", pady=(4, 0))

        tk.Frame(wrap, bg=pal["border_soft"], height=1).pack(fill="x", pady=10)

        rules = nd.get("rules") or []
        if not rules:
            tk.Label(wrap, text="还没有设置提醒档位", bg=pal["paper"], fg=pal["ink_soft"],
                     font=(self.fam_cn, 10), anchor="w").pack(fill="x")
        for idx, rule in enumerate(rules):
            rec = self.find_notify_record(idx) or {}
            status = rec.get("status")
            label = rule.get("label") or _rule_label(rule.get("days"))
            if status == "sent":
                mark, tint, when = "已寄出", "#4F7A52", rec.get("sent_at") or rec.get("at") or ""
            elif status == "failed":
                mark, tint, when = "寄送失败", pal["seal"], rec.get("at") or ""
            elif status == "sending":
                mark, tint, when = "寄送中…", pal["border"], rec.get("at") or ""
            elif status == "skipped":
                mark, tint, when = "已错过", pal["ink_soft"], rec.get("at") or ""
            else:
                mark, tint, when = "尚未触发", pal["ink_soft"], ""

            row = tk.Frame(wrap, bg=pal["paper"])
            row.pack(fill="x", pady=1)
            tk.Label(row, text=label, bg=pal["paper"], fg=pal["ink"],
                     font=(self.fam_cn, 10), width=10, anchor="w").pack(side="left")
            tk.Label(row, text=mark, bg=pal["paper"], fg=tint,
                     font=(self.fam_cn, 10), width=8, anchor="w").pack(side="left")
            tk.Label(row, text=when[:16], bg=pal["paper"], fg=pal["ink_soft"],
                     font=("Consolas", 9), anchor="w").pack(side="left")
            if rec.get("error"):
                tk.Label(wrap, text="　　" + rec["error"][:80], bg=pal["paper"],
                         fg=pal["seal"], font=(self.fam_cn, 9), anchor="w",
                         wraplength=380, justify="left").pack(fill="x")

        if not nd.get("enabled"):
            tk.Label(wrap, text="（打开设置即可开启传书）", bg=pal["paper"],
                     fg=pal["border"], font=(self.fam_cn, 9),
                     anchor="w").pack(fill="x", pady=(10, 0))

        win.update_idletasks()
        w = max(430, win.winfo_reqwidth())
        h = win.winfo_reqheight()
        sw, sh = win.winfo_screenwidth(), win.winfo_screenheight()
        set_geometry(win, w, h, (sw - w) // 2, max(20, (sh - h) // 3))

    # ---------------- 设置面板 ----------------

    def open_settings(self):
        if self._settings is not None:
            try:
                self._settings.win.lift()
                self._settings.win.deiconify()
                return
            except tk.TclError:
                self._settings = None
        self._settings = SettingsPanel(self)

    def close_settings(self):
        if self._settings is not None:
            self._settings.close()

    def apply_settings(self, target_text, thresholds, locked, topmost,
                       autostart=None, notify_cfg=None, secret=None):
        err = None
        parsed, err = parse_target(target_text)
        if parsed is None:
            return err
        self.cfg["target"] = target_text.strip()
        self.cfg["thresholds"] = thresholds
        self.cfg["locked"] = bool(locked)
        self.cfg["always_on_top"] = bool(topmost)
        self.root.attributes("-topmost", bool(topmost))
        # 开机自启：先同步注册表，再落配置。配置里那份只是笔录，
        # 面板下次打开仍按注册表实况显示（见 is_autostart_on）。
        if autostart is not None:
            self.cfg["autostart"] = bool(autostart)
            set_autostart(bool(autostart))
        save_config(self.cfg)

        # 传书设置：只有「影响寄信判断」的字段真的变了，才作废发送履历。
        # 否则你一改配色就把提醒重发一遍，反而成了骚扰。
        # 注意 signature（本机抬头）故意不在这张名单里：它只改信长什么样，
        # 不改变「该不该寄」。改个名字就把所有档位重发一遍是纯骚扰。
        if notify_cfg is not None:
            old_nd = self.cfg.get("notify") or {}
            watched = ("enabled", "rules", "user", "to", "host")
            before = {k: json.dumps(old_nd.get(k), ensure_ascii=False, sort_keys=True)
                      for k in watched}
            self.cfg["notify"] = deep_merge(old_nd, notify_cfg)
            after = {k: json.dumps(self.cfg["notify"].get(k), ensure_ascii=False, sort_keys=True)
                     for k in watched}
            if before != after:
                self.notify_state["history"] = []
                save_notify_state(self.notify_state)
        if secret is not None:
            self.secret = deep_merge(self.secret, secret)
            save_notify_secret(self.secret)

        self._refresh_menu()
        self.target = parsed
        self.parse_err = None
        self.remaining = (self.target - datetime.datetime.now()).total_seconds()
        self.zero_mode = self.remaining <= 0
        self._last_text = None
        self.theme = None
        self._last_notify_check = 0.0      # 让下一轮巡检立刻用新设置重算一次
        self.layout()
        return None

    def factory_reset(self):
        """
        恢复出厂设置：清掉注册表里的数据键，并把内存、窗口、界面一起打回「刚装好」。

        清理范围（都在同一个数据键里，一个键装了全部）：
          目标时刻 / 颜色规则 / 配色 / 邮箱与授权码 / 寄信履历 / 窗口位置与大小。
        不动开机自启 —— 它写在另一个地方（HKCU\\...\\Run，见 set_autostart），
        属于「系统里装了什么」，不是「这个程序里存了什么」；
        而且用户多半正是靠自启才看得见这个按钮，顺手清掉反而添乱。

        界面为什么必须当场刷新：只清数据不刷新，屏幕上还是旧时刻旧配色，
        用户会以为没生效，甚至再点一次。这里让窗口回到默认位置与默认大小、
        配色换回宣纸、倒计时按默认时刻重算 —— 全程不需要重启程序。

        返回 None 表示成功；返回字符串表示失败原因，交给界面提示。
        """
        try:
            self.cfg, self.secret, self.notify_state = reset_factory_data()
        except Exception as exc:                      # noqa: BLE001
            # 删键/重读几乎不会失败（都做了兜底），真失败也不能让程序崩在这儿
            return "恢复出厂失败：%s" % exc

        # --- 内存状态重新对齐：不清这些，下一帧就会拿旧值算 ---
        self.target, self.parse_err = parse_target(self.cfg.get("target"))
        self.remaining = None
        self.zero_mode = False
        self._last_text = None
        self.theme = None
        self.blink = False
        self._last_notify_check = 0.0        # 让下一轮巡检立刻用新设置重算
        self._notify_note = ""
        self._notify_note_at = 0.0

        # --- 界面：配色、置顶、窗口位置尺寸、整幅重绘 ---
        pal = self.cfg["palette"]
        self.root.configure(bg=pal["ink"])
        self.canvas.configure(bg=pal["paper"])
        self.root.attributes("-topmost", bool(self.cfg.get("always_on_top", True)))
        # 位置与尺寸交回 _place_window（它读的已经是刚重置过的 cfg["window"]，
        # x/y 为 None 时自然落回默认点）；persist=False —— 见那里的说明
        self._place_window(persist=False)
        self.W, self.H = self.w, self.h
        self.root.deiconify()
        self.root.lift()

        self._refresh_menu()
        self.layout()
        return None

    def import_shared_from(self, path):
        """
        面板里「从文件导入」的落地动作 —— 导入只有这一条路。
        返回失败说明；成功返回 None。

        两点要紧：**不删文件**（那是用户挑出来的，很可能是他留着的那份
        母本），以及**当场把界面刷成新设置** —— 用户不会为了看一眼效果
        去重启程序。
        """
        status, note = apply_shared_file(path)
        if status != "applied":
            return note
        try:
            self.reload_from_store()
        except Exception as exc:                      # noqa: BLE001
            return "设置已经写入，但界面刷新时出错：%s" % exc
        return None

    def reload_from_store(self):
        """
        从注册表重新读一遍设置，并把窗口按新设置刷新（不重启程序）。

        和 factory_reset 的刷新段是同一套路子，但不清数据、不挪窗口位置 ——
        换的是配色、目标时刻、颜色规则、邮箱设置这些「设置类」的东西。
        """
        self.cfg = load_config()
        self.secret = load_notify_secret()
        self.notify_state = load_notify_state()

        self.target, self.parse_err = parse_target(self.cfg.get("target"))
        self.remaining = ((self.target - datetime.datetime.now()).total_seconds()
                          if self.target else None)
        self.zero_mode = bool(self.remaining is not None and self.remaining <= 0)
        self._last_text = None
        self.theme = None
        self.blink = False
        self._last_notify_check = 0.0      # 让下一轮巡检立刻用新设置重算

        pal = self.cfg["palette"]
        self.root.configure(bg=pal["ink"])
        self.canvas.configure(bg=pal["paper"])
        self.root.attributes("-topmost", bool(self.cfg.get("always_on_top", True)))
        # 尺寸也按新配置来（窗口位置保持不变：导入进来的坐标属于别的机器，
        # 硬套到本机反而会把窗口甩到屏幕外）
        self.w = min(max(MIN_W, int((self.cfg.get("window") or {}).get("w") or 620)),
                     max(MIN_W, self.root.winfo_screenwidth()))
        self.h = min(max(MIN_H, int((self.cfg.get("window") or {}).get("h") or 300)),
                     max(MIN_H, self.root.winfo_screenheight()))
        self.root.deiconify()
        self.root.lift()
        self._restore_chrome()
        set_geometry(self.root, self.w, self.h, self.x, self.y)
        self.W, self.H = self.w, self.h

        self._refresh_menu()
        self.layout()

    def run(self):
        self.root.mainloop()


# --------------------------------------------------------------------------
# 设置面板
# --------------------------------------------------------------------------

class ExportPicker:
    """
    导出共用设置时那个「挑哪几项」的小窗。

    为什么非得有它：用户要同步的是十几台机器，绝大多数设置想配成一样，
    偏偏每台机器的目标时刻各不相同（各有各要倒计的事）。不挑的话，一次
    同步就把所有机器的时刻冲成同一个 —— 恰是他最不能接受的事。
    所以默认把「目标时刻」留成不勾，其余全勾；想连时刻一起发，自己点上。

    勾选结果会记住（见 load_shared_selection）：一次配十台机器，每次要的
    几乎总是同一套，不该让他每条重新勾一遍。
    """

    W = 440

    def __init__(self, app, on_pick):
        self.app = app
        self.on_pick = on_pick
        pal = app.cfg["palette"]
        self.pal = pal
        self.sel = load_shared_selection()
        self.rows = []              # [(key, 那个方框 Label)]
        self._pt = None             # 拖标题栏时的按下点

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)
        self.body = tk.Frame(self.win, bg=pal["paper"])
        self.body.pack(fill="both", expand=True, padx=3, pady=3)

        self._build_header()
        for spec in SHARED_ITEMS:
            self._row(spec)
        self._build_footer()

        self.win.update_idletasks()
        self._center()
        self.win.bind("<Escape>", lambda e: self.close())
        try:
            self.win.grab_set()     # 挑完再回设置面板，避免两层窗口打架
        except tk.TclError:
            pass

    # ---- 结构 ----

    def _build_header(self):
        pal, app = self.pal, self.app
        head = tk.Frame(self.body, bg=pal["ink"], height=34)
        head.pack(fill="x")
        head.pack_propagate(False)
        tk.Label(head, text="　导出哪些设置", bg=pal["ink"], fg=pal["paper"],
                 font=(app.fam_cn, 11, "bold")).pack(side="left", padx=10)
        close = tk.Label(head, text="✕", bg=pal["ink"], fg=pal["border_soft"],
                         font=("Segoe UI", 11), cursor="hand2", padx=12)
        close.pack(side="right", fill="y")
        close.bind("<Button-1>", lambda e: self.close())
        close.bind("<Enter>",
                   lambda e: close.configure(bg=pal["seal"], fg="#FFF8EC"))
        close.bind("<Leave>",
                   lambda e: close.configure(bg=pal["ink"], fg=pal["border_soft"]))
        head.bind("<Button-1>", self._drag_start)
        head.bind("<B1-Motion>", self._drag_move)

        tk.Label(self.body,
                 text="　勾上的才会写进文件。没勾的那一项，对方机器上原来\n"
                      "　的设置会原样留着 —— 不会被这台的样子覆盖掉。",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left").pack(fill="x", padx=16, pady=(8, 4))

    def _row(self, spec):
        pal, app, key = self.pal, self.app, spec["key"]
        row = tk.Frame(self.body, bg=pal["paper"])
        row.pack(fill="x", padx=16, pady=(4, 0))

        box = tk.Label(row, text="", bg=pal["paper"], font=(app.fam_cn, 12),
                       cursor="hand2", width=2)
        box.pack(side="left", anchor="n")

        txt = tk.Frame(row, bg=pal["paper"])
        txt.pack(side="left", fill="x", expand=True, padx=(4, 0))
        tk.Label(txt, text=spec["label"], bg=pal["paper"], fg=pal["ink"],
                 font=(app.fam_cn, 10), anchor="w").pack(fill="x")
        tk.Label(txt, text=spec["hint"], bg=pal["paper"], fg=pal["border"],
                 font=(app.fam_cn, 8), anchor="w", justify="left").pack(fill="x")

        # 整行和方框都能点 —— 字小、行窄，只让那个小方框能点太难点中
        for w in (row, box, txt):
            w.bind("<Button-1>", lambda e, k=key: self._toggle(k))
        self.rows.append((key, box))
        self._paint(key)

    def _build_footer(self):
        pal, app = self.pal, self.app
        tk.Frame(self.body, bg=pal["border_soft"], height=1).pack(
            fill="x", padx=16, pady=(12, 0))
        bar = tk.Frame(self.body, bg=pal["paper"])
        bar.pack(fill="x", padx=16, pady=10)

        for text, act in (("全选", self._pick_all), ("全不选", self._pick_none)):
            b = tk.Label(bar, text=text, bg=pal["paper"], fg=pal["ink_soft"],
                         font=(app.fam_cn, 9), cursor="hand2")
            b.pack(side="left", padx=(0, 12))
            b.bind("<Button-1>", lambda e, f=act: f())
            b.bind("<Enter>", lambda e, w=b: w.configure(fg=pal["seal"]))
            b.bind("<Leave>", lambda e, w=b: w.configure(fg=pal["ink_soft"]))

        go = tk.Label(bar, text="确 定", bg=pal["paper"], fg=pal["ink"],
                      font=(app.fam_cn, 11, "bold"), cursor="hand2",
                      padx=14, pady=4, relief="solid", bd=1)
        go.pack(side="right")
        go.bind("<Button-1>", lambda e: self._confirm())
        cancel = tk.Label(bar, text="取消", bg=pal["paper"], fg=pal["ink_soft"],
                          font=(app.fam_cn, 10), cursor="hand2", padx=10, pady=4)
        cancel.pack(side="right", padx=(0, 8))
        cancel.bind("<Button-1>", lambda e: self.close())

    # ---- 行为 ----

    def _paint(self, key):
        """按当前勾选把那个方框画出来（☑ 实心勾 / ☐ 空心）。"""
        for k, box in self.rows:
            if k != key:
                continue
            on = bool(self.sel.get(key))
            box.configure(text="☑" if on else "☐",
                          fg=self.pal["seal"] if on else self.pal["border"])

    def _toggle(self, key):
        self.sel[key] = not self.sel.get(key)
        self._paint(key)

    def _pick_all(self):
        for key in shared_item_keys():
            self.sel[key] = True
            self._paint(key)

    def _pick_none(self):
        for key in shared_item_keys():
            self.sel[key] = False
            self._paint(key)

    def _confirm(self):
        picked = [k for k in shared_item_keys() if self.sel.get(k)]
        if not picked:
            # 空文件不是「什么都不改」，它会让对方以为导入成功了 —— 更糟
            messagebox.showwarning("还没挑东西",
                                   "至少勾一项再导出。\n\n"
                                   "一项都不带的文件拷到别的机器上什么也不会改，"
                                   "但那边会显示「导入成功」，反而更难发现问题。")
            return
        save_shared_selection(self.sel)
        cb, sel = self.on_pick, dict(self.sel)
        self.close()
        if cb:
            cb(sel)                  # 关掉自己再回调：后面的保存对话框才不会挂在这扇窗上

    def _drag_start(self, event):
        self._pt = (event.x_root - self.win.winfo_x(),
                    event.y_root - self.win.winfo_y())

    def _drag_move(self, event):
        if not self._pt:
            return
        # 拖到左屏 / 上屏时坐标是负的，必须走 set_window_pos，否则窗口会「拖不动」
        set_window_pos(self.win, event.x_root - self._pt[0],
                       event.y_root - self._pt[1])

    def _center(self):
        sw = self.win.winfo_screenwidth()
        sh = self.win.winfo_screenheight()
        w = max(self.W, self.win.winfo_reqwidth())
        h = self.win.winfo_reqheight()
        top = max(8, min((sh - h) // 2 - 40, sh - h - 16))
        set_geometry(self.win, w, h, (sw - w) // 2, top)

    def close(self):
        try:
            self.win.grab_release()
        except (tk.TclError, AttributeError):
            pass
        try:
            self.win.destroy()
        except tk.TclError:
            pass


class SettingsPanel:
    """古风配色设置面板（无系统边框，自绘标题栏）。"""

    W = 470                 # 单列宽（屏幕不够宽时的兜底）
    WIDE = 900              # 两列宽（正常情况走这个）

    def __init__(self, app):
        self.app = app
        pal = app.cfg["palette"]
        self.pal = pal
        self.rows = []          # [(frame, days_var, color_value, bg_value, widgets...)]
        self.notify_rows = []   # [(days_var, on_var, row)] —— 传书提醒档位
        self._color_popup = None
        self._color_popup_for = None
        self._picker = None     # 「导出哪些设置」那扇小窗；面板关掉时一并带走
        self._updating = False  # 正在检查/下载更新，防止重复点按钮
        # 两列排版：内容越加越长，单列在 720p 高的机器上会顶出屏幕，
        # 下半截得靠挪窗口才看得见。分成两列高度差不多减半 —— 宽度富余得很，
        # 高度才是稀缺的。（窄屏兜底：屏幕不够宽就退回单列宽。）
        self.W = min(SettingsPanel.WIDE,
                     max(SettingsPanel.W, app.root.winfo_screenwidth() - 60))

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)

        self.body = tk.Frame(self.win, bg=pal["paper"])
        self.body.pack(fill="both", expand=True, padx=3, pady=3)

        self._build_header()
        self._build_columns()
        self._build_footer()
        self._fit_height()

        self.win.bind("<Escape>", lambda e: self.close())
        # 无边框窗口没有系统滚动条，滚轮得自己接（见 _on_wheel）
        self.win.bind_all("<MouseWheel>", self._on_wheel)
        self.entry.focus_set()

    # ---- 结构 ----

    def _build_columns(self):
        """
        内容分左右两列，装进一层可上下滚的 Canvas。

        左列：倒计到什么时候 / 颜色怎么变 / 怎么同步给别的机器
        右列：窗口怎么摆 / 要不要寄信
        这么分不是照重要性，是照「一块内容有多高」配平的 —— 传书那一块自带
        好几行，跟它同列的就得矮一点；否则一列顶到底、另一列空半截，
        面板高度由高的那一列说了算，配平了才真的省下高度。
        """
        pal = self.pal
        self.canvas = tk.Canvas(self.body, bg=pal["paper"], highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)
        inner = tk.Frame(self.canvas, bg=pal["paper"])
        self._inner_win = self.canvas.create_window((0, 0), window=inner,
                                                    anchor="nw")
        inner.bind("<Configure>",
                   lambda e: self.canvas.configure(
                       scrollregion=self.canvas.bbox("all")))
        # canvas 变宽变窄时把内容区拉齐，两列才不会挤在左边一小条里
        self.canvas.bind("<Configure>", self._on_canvas_resize)
        self.inner = inner

        cols = tk.Frame(inner, bg=pal["paper"])
        cols.pack(fill="both", expand=True)
        # 用 grid 而不是 pack：pack(expand=True) 只能均分「多出来的」空间，
        # 两列内容本身宽度不一样时（左列那几个长复选框），结果是一宽一窄。
        # uniform 加 weight 才是真·等宽 —— 取两列里较宽的那个为准。
        cols.grid_columnconfigure(0, weight=1, uniform="col")
        cols.grid_columnconfigure(1, weight=1, uniform="col")
        cols.grid_rowconfigure(0, weight=1)
        self.col_l = tk.Frame(cols, bg=pal["paper"])
        self.col_l.grid(row=0, column=0, sticky="nsew", padx=(10, 4))
        self.col_r = tk.Frame(cols, bg=pal["paper"])
        self.col_r.grid(row=0, column=1, sticky="nsew", padx=(4, 10))

        self._build_target(self.col_l)
        self._build_thresholds(self.col_l)
        self._build_shared(self.col_l)
        self._build_window(self.col_r)
        self._build_notify(self.col_r)

    def _on_canvas_resize(self, event):
        try:
            self.canvas.itemconfigure(self._inner_win, width=event.width)
            # 顺手把滚动范围刷一遍：inner 的尺寸未必变（比如只是 canvas 变矮了），
            # 光靠 inner 的 <Configure> 会漏掉这种情况，于是滚轮「完全没反应」。
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        except tk.TclError:
            pass

    def _fit_height(self):
        """面板高度压到屏幕放得下为止；实在放不下的部分交给滚轮。"""
        self.win.update_idletasks()
        req_h = self.inner.winfo_reqheight()
        req_w = self.inner.winfo_reqwidth()
        # 150 = 标题栏 38 + 页脚约 76 + 外框 6，再加一点余量。
        # 只减 110 的话，面板总高会正好顶到屏幕边 —— 底部按钮被任务栏压住。
        room = max(260, self.win.winfo_screenheight() - 150)
        # 宽度跟着内容走（两列等宽后可能比预设的 W 更宽一点），
        # 写死 W-6 会把较宽那一列的内容裁掉一截。
        self.canvas.configure(height=min(req_h, room),
                              width=max(self.W - 6, req_w))
        self.win.update_idletasks()
        # 显式设一次滚动范围：到这里 inner 才刚布局完，
        # 它的 <Configure> 未必已经跑过一遍。
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        self._center()

    def _on_wheel(self, event):
        """内容比面板高时，滚轮上下滚（比把整个窗口挪来挪去自然得多）。"""
        try:
            if not self.canvas.winfo_exists():
                return
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        except tk.TclError:
            pass

    def _build_header(self):
        pal = self.pal
        self.header = tk.Frame(self.body, bg=pal["ink"], height=38)
        self.header.pack(fill="x")
        self.header.pack_propagate(False)
        tk.Label(self.header, text="　設 　置", bg=pal["ink"], fg=pal["paper"],
                 font=(self.app.fam_cn, 12, "bold")).pack(side="left", padx=12)
        # 版本号摆在标题右边：用户升完级总得有个地方确认「我到底升上没有」，
        # 否则新旧版本界面一模一样，点了更新跟没点似的。
        tk.Label(self.header, text="v" + APP_VERSION, bg=pal["ink"],
                 fg=pal["border_soft"], font=("Segoe UI", 9)).pack(
            side="left", padx=(0, 2), pady=(6, 0), anchor="sw")
        close = tk.Label(self.header, text="✕", bg=pal["ink"], fg=pal["border_soft"],
                         font=("Segoe UI", 11), cursor="hand2", padx=14)
        close.pack(side="right", fill="y")
        close.bind("<Button-1>", lambda e: self.close())
        close.bind("<Enter>", lambda e: close.configure(bg=pal["seal"], fg="#FFF8EC"))
        close.bind("<Leave>", lambda e: close.configure(bg=pal["ink"], fg=pal["border_soft"]))
        self._drag_bind(self.header)

    def _section(self, text, parent=None):
        # parent 默认 self.body：页脚之类挂在面板本体上的仍走老写法
        wrap = tk.Frame(parent or self.body, bg=self.pal["paper"])
        wrap.pack(fill="x", padx=18, pady=(14, 4))
        tk.Label(wrap, text=text, bg=self.pal["paper"], fg=self.pal["ink"],
                 font=(self.app.fam_cn, 11, "bold")).pack(side="left")
        tk.Frame(wrap, bg=self.pal["border_soft"], height=1).pack(
            side="left", fill="x", expand=True, padx=(10, 0), pady=(7, 0))
        return wrap

    def _build_target(self, parent):
        app, pal = self.app, self.pal

        # --- 目标时间 ---
        self._section("目标时刻", parent)
        box = tk.Frame(parent, bg=pal["paper"])
        box.pack(fill="x", padx=18)
        self.entry = tk.Entry(box, font=(app.fam_num, 17, "bold"), justify="center",
                              bg="#FFFBF2", fg=pal["ink"], relief="flat",
                              insertbackground=pal["seal"],
                              highlightthickness=1, highlightbackground=pal["border_soft"],
                              highlightcolor=pal["seal"])
        self.entry.pack(fill="x", ipady=7)
        self.entry.insert(0, app.cfg.get("target", ""))
        self.entry.bind("<KeyRelease>", lambda e: self._preview())
        self.entry.bind("<Return>", lambda e: self._preview())

        self.preview = tk.Label(parent, text="", bg=pal["paper"], fg=pal["ink_soft"],
                                font=(app.fam_cn, 10), anchor="w")
        self.preview.pack(fill="x", padx=20, pady=(5, 0))

        tk.Label(parent, text="　格式：月.日.时.分　数字之间随便填什么都能认",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w").pack(fill="x", padx=18, pady=(3, 0))
        tk.Label(parent, text="　　　例：10.1.11.30 ／ 10 1 0330 ／ 10.1 8 ／ 10.1/2，32",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w").pack(fill="x", padx=18, pady=(1, 0))
        tk.Label(parent, text="　　　时分秒写在一起也认（0330＝03:30）；"
                             "年份写在最前面，如 2026.10.1",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w").pack(fill="x", padx=18, pady=(1, 0))
        self._preview()

    def _build_thresholds(self, parent):
        app, pal = self.app, self.pal

        # --- 颜色规则 ---
        head = self._section("颜色规则", parent)
        tk.Label(head, text="剩余时间 ≤ 阈值时切换", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="right")

        self.rules = tk.Frame(parent, bg=pal["paper"])
        self.rules.pack(fill="x", padx=18)
        for item in app.cfg.get("thresholds", []):
            self._add_row(item.get("days"), item.get("color"), item.get("bg"))

        add = tk.Label(parent, text="＋  添加一条规则", bg=pal["paper"], fg=pal["border"],
                       font=(app.fam_cn, 10), cursor="hand2", anchor="w")
        add.pack(fill="x", padx=20, pady=(6, 0))
        add.bind("<Button-1>", lambda e: self._add_row(1, "#B03A2E", None))
        add.bind("<Enter>", lambda e: add.configure(fg=pal["seal"]))
        add.bind("<Leave>", lambda e: add.configure(fg=pal["border"]))

    def _build_window(self, parent):
        app, pal = self.app, self.pal

        # --- 窗口选项 ---
        self._section("窗口", parent)
        self._build_size_row(parent)
        self.var_lock = tk.BooleanVar(value=bool(app.cfg.get("locked")))
        self.var_top = tk.BooleanVar(value=bool(app.cfg.get("always_on_top", True)))
        # 自启勾选框的初值读注册表现状而非配置：启动项被清掉时不能显示假状态
        self.var_autostart = tk.BooleanVar(value=is_autostart_on())
        self.var_autoupd = tk.BooleanVar(
            value=bool(app.cfg.get("auto_update_check", True)))
        for var, text in ((self.var_lock, "锁定窗口尺寸（禁止拖拽边缘缩放）"),
                          (self.var_top, "窗口总在最前"),
                          (self.var_autostart, "开机自动运行（写入当前用户启动项）"),
                          (self.var_autoupd, "自动检查新版本（每七天一次，静默不打扰）")):
            tk.Checkbutton(parent, text="  " + text, variable=var,
                           bg=pal["paper"], fg=pal["ink"], selectcolor="#FFFBF2",
                           activebackground=pal["paper"], activeforeground=pal["seal"],
                           font=(app.fam_cn, 10), anchor="w", bd=0,
                           highlightthickness=0).pack(fill="x", padx=20)

        self._preview()

    def _build_size_row(self, parent):
        """
        窗口尺寸：把「现在多大」写在面板上，并且能直接填数字改。

        显示这一项是用户提的：窗口一直是靠拖边缘调的，拖完到底多大没有一个
        地方写着。给一个准数之后，既能照着复原，也能让几台机器调成一样。
        """
        app, pal = self.app, self.pal
        row = tk.Frame(parent, bg=pal["paper"])
        row.pack(fill="x", padx=18, pady=(0, 4))

        tk.Label(row, text="尺寸（宽 × 高）", bg=pal["paper"], fg=pal["ink"],
                 font=(app.fam_cn, 10)).pack(side="left")

        self.var_w = tk.StringVar()
        self.var_h = tk.StringVar()
        self.entry_w = tk.Entry(row, textvariable=self.var_w, width=6,
                                font=(app.fam_num, 11), justify="center",
                                bg="#FFFBF2", fg=pal["ink"], relief="flat",
                                insertbackground=pal["seal"],
                                highlightthickness=1,
                                highlightbackground=pal["border_soft"],
                                highlightcolor=pal["seal"])
        self.entry_w.pack(side="left", padx=(8, 0), ipady=2)
        self.entry_w.bind("<Return>", lambda e: self._apply_size())

        tk.Label(row, text="×", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10)).pack(side="left", padx=6)

        self.entry_h = tk.Entry(row, textvariable=self.var_h, width=6,
                                font=(app.fam_num, 11), justify="center",
                                bg="#FFFBF2", fg=pal["ink"], relief="flat",
                                insertbackground=pal["seal"],
                                highlightthickness=1,
                                highlightbackground=pal["border_soft"],
                                highlightcolor=pal["seal"])
        self.entry_h.pack(side="left", ipady=2)
        self.entry_h.bind("<Return>", lambda e: self._apply_size())

        apply_btn = tk.Label(row, text="应用", bg=pal["paper"], fg=pal["ink_soft"],
                             font=(app.fam_cn, 10), cursor="hand2",
                             padx=8, pady=2, relief="solid", bd=1)
        apply_btn.pack(side="left", padx=(12, 0))
        apply_btn.bind("<Button-1>", lambda e: self._apply_size())
        apply_btn.bind("<Enter>",
                       lambda e: apply_btn.configure(fg=pal["seal"]))
        apply_btn.bind("<Leave>",
                       lambda e: apply_btn.configure(fg=pal["ink_soft"]))

        tk.Label(parent, text="　拖窗口边缘也能改；勾了「锁定窗口尺寸」就改不动。",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w").pack(fill="x", padx=18, pady=(0, 6))

        self._sync_size()
        self._poll_size()

    def _sync_size(self):
        """把主窗口当前尺寸填进两个输入框。用户正在编辑时不动，免得打断他。"""
        if not hasattr(self, "entry_w"):
            return
        try:
            if self.win.focus_displayof() in (self.entry_w, self.entry_h):
                return
        except (tk.TclError, AttributeError):
            pass
        w = int(self.app.W or self.app.w or 0)
        h = int(self.app.H or self.app.h or 0)
        if self.var_w.get() != str(w):
            self.var_w.set(str(w))
        if self.var_h.get() != str(h):
            self.var_h.set(str(h))

    def _poll_size(self):
        """窗口被拖着改大小时，面板里的数字跟着变（每半秒看一眼，开销可忽略）。"""
        try:
            if not self.win.winfo_exists():
                return
            self._sync_size()
            self.win.after(500, self._poll_size)
        except tk.TclError:
            return          # 面板已经关了，轮询自然停下

    def _apply_size(self):
        err = self.app.resize_to(self.var_w.get(), self.var_h.get())
        self._sync_size()
        self.msg.configure(text=err if err else
                           "窗口已改成 %d × %d" % (self.app.w, self.app.h),
                           fg=self.pal["seal"] if err else self.pal["ink_soft"])

    # ---- 传书设置 ----

    def _build_notify(self, parent):
        app, pal = self.app, self.pal
        nd = app.cfg.get("notify") or {}

        head = self._section("传书 · 邮件提醒", parent)
        tk.Label(head, text="跨过档位即寄信", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="right")

        wrap = tk.Frame(parent, bg=pal["paper"])
        wrap.pack(fill="x", padx=18)

        self.var_notify = tk.BooleanVar(value=bool(nd.get("enabled")))
        tk.Checkbutton(wrap, text="  启用邮件提醒（关掉则只变色、不发信）",
                       variable=self.var_notify, bg=pal["paper"], fg=pal["ink"],
                       selectcolor="#FFFBF2", activebackground=pal["paper"],
                       activeforeground=pal["seal"], font=(app.fam_cn, 10),
                       anchor="w", bd=0, highlightthickness=0).pack(fill="x")

        form = tk.Frame(wrap, bg=pal["paper"])
        form.pack(fill="x", pady=(6, 0))

        def field(label, value, masked=False):
            row = tk.Frame(form, bg=pal["paper"])
            row.pack(fill="x", pady=2)
            tk.Label(row, text=label, bg=pal["paper"], fg=pal["ink_soft"],
                     font=(app.fam_cn, 10), width=7, anchor="w").pack(side="left")
            ent = tk.Entry(row, font=(app.fam_num, 10), bg="#FFFBF2", fg=pal["ink"],
                           relief="flat", insertbackground=pal["seal"],
                           highlightthickness=1, highlightbackground=pal["border_soft"],
                           highlightcolor=pal["seal"],
                           show=("●" if masked else ""))
            ent.insert(0, value or "")
            ent.pack(side="left", fill="x", expand=True, ipady=3)
            return ent

        # 服务商下拉：选好就把服务器地址带出来，省得用户记端口
        row = tk.Frame(form, bg=pal["paper"])
        row.pack(fill="x", pady=2)
        tk.Label(row, text="邮箱服务", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=7, anchor="w").pack(side="left")
        self.var_provider = tk.StringVar(value=nd.get("provider") or "QQ 邮箱")
        picker = tk.OptionMenu(row, self.var_provider, *PROVIDER_NAMES,
                               command=self._on_provider)
        picker.configure(bg="#FFFBF2", fg=pal["ink"], activebackground="#FFFBF2",
                         font=(app.fam_cn, 10), highlightthickness=1, bd=0,
                         relief="flat", anchor="w",
                         highlightbackground=pal["border_soft"])
        picker["menu"].configure(font=(app.fam_cn, 10), bg="#FFFBF2", fg=pal["ink"],
                                 activebackground=pal["seal"], activeforeground="#FFF8EC")
        picker.pack(side="left", fill="x", expand=True)

        self.entry_user = field("发件邮箱", nd.get("user"))
        self.entry_pass = field("授权码", (app.secret or {}).get("smtp_password"), masked=True)
        self.entry_to = field("收件邮箱", nd.get("to"))
        self.entry_sign = field("本机抬头", nd.get("signature"))
        self.entry_host = field("服务器", nd.get("host"))

        tk.Label(wrap, text="　授权码非登录密码，要在邮箱里单独申请；收件邮箱留空即发给自己",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left", wraplength=434).pack(fill="x", pady=(2, 0))
        tk.Label(wrap, text="　本机抬头用于分辨是哪台电脑寄的，会出现在发件人、主题前缀"
                            "和正文落款三处；留空即不加。默认取计算机名「%s」"
                            % machine_name(),
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left", wraplength=434).pack(fill="x", pady=(1, 0))

        sub = tk.Frame(wrap, bg=pal["paper"])
        # 上面那两行说明紧跟着服务器输入框，不留够空档会跟「提醒档位」粘在一起
        sub.pack(fill="x", pady=(16, 0))
        tk.Label(sub, text="提醒档位", bg=pal["paper"], fg=pal["ink"],
                 font=(app.fam_cn, 10, "bold")).pack(side="left")
        tk.Label(sub, text="剩余 ≤ 该天数时寄一封", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="left", padx=(8, 0))

        self.rule_box = tk.Frame(wrap, bg=pal["paper"])
        self.rule_box.pack(fill="x")
        for item in nd.get("rules") or []:
            self._add_rule_row(item.get("days"), item.get("enabled", True))

        adder = tk.Label(wrap, text="＋  添加一档", bg=pal["paper"], fg=pal["border"],
                         font=(app.fam_cn, 10), cursor="hand2", anchor="w")
        adder.pack(fill="x", pady=(4, 0), padx=(2, 0))
        adder.bind("<Button-1>", lambda e: self._add_rule_row(1, True))
        adder.bind("<Enter>", lambda e: adder.configure(fg=pal["seal"]))
        adder.bind("<Leave>", lambda e: adder.configure(fg=pal["border"]))

        bar = tk.Frame(wrap, bg=pal["paper"])
        bar.pack(fill="x", pady=(10, 0))
        self.test_btn = tk.Label(bar, text="试寄一封", bg=pal["paper"], fg=pal["ink"],
                                 font=(app.fam_cn, 10), cursor="hand2",
                                 padx=12, pady=3, highlightthickness=1,
                                 highlightbackground=pal["border_soft"])
        self.test_btn.pack(side="left")
        self.test_btn.bind("<Button-1>", lambda e: self._test_send())
        self.test_btn.bind("<Enter>", lambda e: self.test_btn.configure(fg=pal["seal"]))
        self.test_btn.bind("<Leave>", lambda e: self.test_btn.configure(fg=pal["ink"]))

        self.test_msg = tk.Label(bar, text="", bg=pal["paper"], fg=pal["ink_soft"],
                                 font=(app.fam_cn, 9), anchor="w", justify="left",
                                 wraplength=250)
        self.test_msg.pack(side="left", padx=(10, 0))

    def _on_provider(self, _value=None):
        """换服务商就把服务器地址一并带出来。"""
        host, _port, _ssl = self._provider_params(self.var_provider.get())
        self.entry_host.delete(0, "end")
        self.entry_host.insert(0, host)

    def _provider_params(self, name):
        for item in SMTP_PROVIDERS:
            if item[0] == name:
                return item[1], item[2], item[3]
        return "", 465, True

    def _add_rule_row(self, days, enabled=True):
        pal = self.pal
        row = tk.Frame(self.rule_box, bg=pal["paper"])
        row.pack(fill="x", pady=2)

        on = tk.BooleanVar(value=bool(enabled))
        tk.Checkbutton(row, variable=on, bg=pal["paper"], activebackground=pal["paper"],
                       selectcolor="#FFFBF2", bd=0,
                       highlightthickness=0).pack(side="left")

        tk.Label(row, text="剩余 ≤", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left")

        days_var = tk.StringVar(value=("%g" % float(days)) if days is not None else "2")
        ent = tk.Entry(row, textvariable=days_var, width=5, justify="center",
                       font=(self.app.fam_num, 11, "bold"),
                       bg="#FFFBF2", fg=pal["ink"], relief="flat",
                       insertbackground=pal["seal"],
                       highlightthickness=1, highlightbackground=pal["border_soft"],
                       highlightcolor=pal["seal"])
        ent.pack(side="left", padx=5, ipady=3)

        tk.Label(row, text="天", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left")

        record = {"days": days_var, "on": on, "row": row}
        rm = tk.Label(row, text="✕", bg=pal["paper"], fg=pal["border_soft"],
                      font=("Segoe UI", 10), cursor="hand2", padx=8)
        rm.pack(side="right")
        rm.bind("<Button-1>", lambda e: self._remove_rule_row(record))
        rm.bind("<Enter>", lambda e: rm.configure(fg=pal["seal"]))
        rm.bind("<Leave>", lambda e: rm.configure(fg=pal["border_soft"]))
        self.notify_rows.append(record)

    def _remove_rule_row(self, record):
        if record in self.notify_rows:
            self.notify_rows.remove(record)
        try:
            record["row"].destroy()
        except tk.TclError:
            pass

    def _collect_notify(self):
        rules = []
        for rec in self.notify_rows:
            raw = rec["days"].get().strip()
            try:
                days = float(raw)
            except ValueError:
                return None, "提醒档位要填天数，可带小数（0.5 即 12 小时）"
            if days < 0:
                return None, "提醒档位的天数不能为负"
            rules.append({
                "days": days,
                "enabled": bool(rec["on"].get()),
                "label": _rule_label(days),
            })

        provider = self.var_provider.get()
        host, port, use_ssl = self._provider_params(provider)
        host = self.entry_host.get().strip() or host

        # 抬头要进 From 和 Subject，太长会把主题挤爆，也容易被邮件服务商判成
        # 可疑标题；换行更是邮件头注入。两者都在这里挡掉。
        sign = sanitize_signature(self.entry_sign.get())
        if len(sign) > SIGNATURE_LIMIT:
            return None, "本机抬头最多 %d 个字，现在的太长了" % SIGNATURE_LIMIT

        cfg = {
            "enabled": bool(self.var_notify.get()),
            "provider": provider,
            "host": host,
            "port": port,
            "use_ssl": use_ssl,
            "user": self.entry_user.get().strip(),
            "to": self.entry_to.get().strip(),
            "signature": sign,
            "rules": rules,
        }
        secret = {"smtp_password": self.entry_pass.get().strip()}
        return (cfg, secret), None

    def _test_send(self):
        """拿面板里当下填的值试寄一封，不写盘也不动履历。"""
        # 抬头先校验：试寄和正式寄必须同一套规矩，不然「试寄通过、保存被拒」
        # 会让人以为是发信出了问题。
        sign = sanitize_signature(self.entry_sign.get())
        if len(sign) > SIGNATURE_LIMIT:
            self.test_msg.configure(
                text="✕ 本机抬头最多 %d 个字" % SIGNATURE_LIMIT, fg=self.pal["seal"])
            return

        nd = self.app.cfg.setdefault("notify", {})
        # 试寄只「借用」面板里的值，寄完立刻还回去。
        # 不还的后果很隐蔽：点了试寄又关掉面板不保存，内存里的配置
        # 已经被悄悄改掉，程序之后按这次「没保存」的值寄信 ——
        # 用户看到的是「我明明没保存，怎么生效了」。盘上的配置没动，
        # 所以重启又变回去，最容易查错方向。
        backup = json.loads(json.dumps(nd, ensure_ascii=False))
        pwd_backup = self.app.secret.get("smtp_password")
        try:
            provider = self.var_provider.get()
            host, port, use_ssl = self._provider_params(provider)
            nd["provider"] = provider
            nd["host"] = self.entry_host.get().strip() or host
            nd["port"] = port
            nd["use_ssl"] = use_ssl
            nd["user"] = self.entry_user.get().strip()
            nd["to"] = self.entry_to.get().strip()
            # 试寄也要带上抬头，否则用户没法先确认「收件箱里长什么样」
            nd["signature"] = sign
            self.app.secret["smtp_password"] = self.entry_pass.get().strip()

            token, err = self.app.send_test_mail()
        finally:
            self.app.cfg["notify"] = backup
            if pwd_backup is None:
                self.app.secret.pop("smtp_password", None)
            else:
                self.app.secret["smtp_password"] = pwd_backup

        if err:
            self.test_msg.configure(text="✕ " + err, fg=self.pal["seal"])
            return
        self.test_msg.configure(text="正在寄出…", fg=self.pal["ink_soft"])
        self._poll_test(token, 0)

    def _poll_test(self, token, ticks):
        """等发信进程回话。它在另一个进程里跑，所以界面一直能动。"""
        data = reg_store_read("notify_test_result", None)
        if data is not None:
            reg_store_delete("notify_test_result")
            if isinstance(data, dict) and data.get("token") == token:
                if data.get("ok"):
                    self.test_msg.configure(text="✓ 已寄出，去收件箱看看", fg="#4F7A52")
                else:
                    self.test_msg.configure(
                        text="✕ " + (data.get("error") or "未知错误")[:90],
                        fg=self.pal["seal"])
                return
        if ticks > 60:
            self.test_msg.configure(text="✕ 等了一分钟没回音，检查网络或授权码",
                                    fg=self.pal["seal"])
            return
        try:
            self.win.after(500, lambda: self._poll_test(token, ticks + 1))
        except tk.TclError:
            pass

    def _build_shared(self, parent):
        """
        「多机共用设置」一节。

        为什么放在面板里而不是做成命令行参数：会用这个功能的人手上有十来台
        机器要配成一样，他不会为了这个去开命令行。面板里点一下导出、
        把文件拷过去、在对方机器上导入，三步就完事。
        """
        app, pal = self.app, self.pal
        self._section("多机共用设置", parent)


        tk.Label(parent,
                 text="　把设置导成一份文件，拷到别的机器上；在那台机器的设置面板里\n"
                      "　点「从文件导入…」选中它，即刻生效（那份文件会留着，不删）。",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left").pack(fill="x", padx=18, pady=(3, 0))
        tk.Label(parent,
                 text="　导出时可以一项一项挑 —— 不挑的那项，对方机器上原样保留。",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left").pack(fill="x", padx=18, pady=(1, 0))
        tk.Label(parent,
                 text="　本机抬头与开机自启不在文件里 —— 每台机器各自设。",
                 bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                 anchor="w", justify="left").pack(fill="x", padx=18, pady=(1, 0))

        bar = tk.Frame(parent, bg=pal["paper"])
        bar.pack(fill="x", padx=18, pady=(8, 0))
        # 导出会顺带把面板里填的东西先保存下来（见 save(then_export=True)），
        # 所以这里不用提醒「先保存」—— 用户点了就是「我眼前这份，拿出去」。
        for text, act in (("导出共用设置…", lambda: self.save(then_export=True)),
                          ("从文件导入…", self._import_shared)):
            btn = tk.Label(bar, text=text, bg=pal["paper"], fg=pal["ink_soft"],
                           font=(app.fam_cn, 10), cursor="hand2", padx=10, pady=4,
                           relief="solid", bd=1)
            btn.pack(side="left", padx=(0, 10))
            btn.bind("<Button-1>", lambda e, f=act: f())
            btn.bind("<Enter>", lambda e, b=btn: b.configure(fg=pal["seal"]))
            btn.bind("<Leave>", lambda e, b=btn: b.configure(fg=pal["ink_soft"]))

        # 最近一次导入的结果：让用户能确认「文件到底吃进去了没有」，
        # 而不用去翻注册表。失败信息也显示在这里（文件会留着不删）。
        last = shared_last_result()
        if last:
            status = last.get("status")
            if status == "applied":
                tip, color = "上次导入：成功（%s）" % last.get("at", ""), "#4F7A52"
            elif status == "skipped":
                tip, color = "上次：文件内容与上次相同，已跳过（%s）" % last.get("at", ""), pal["ink_soft"]
            else:
                tip, color = "上次没读成：%s" % last.get("note", ""), pal["seal"]
        else:
            tip, color = "（还没导入过。导出一份、拷过去、在对方机器上导入即可。）", pal["border"]
        self.lbl_shared = tk.Label(parent, text="　" + tip, bg=pal["paper"],
                                   fg=color, font=(app.fam_cn, 9), anchor="w",
                                   justify="left", wraplength=(self.W // 2) - 60)
        self.lbl_shared.pack(fill="x", padx=18, pady=(6, 0))

    def _build_footer(self):
        pal = self.pal
        tk.Frame(self.body, bg=pal["border_soft"], height=1).pack(
            fill="x", padx=18, pady=(14, 0))
        bar = tk.Frame(self.body, bg=pal["paper"])
        bar.pack(fill="x", padx=18, pady=12)
        self.msg = tk.Label(bar, text="", bg=pal["paper"], fg=pal["seal"],
                            font=(self.app.fam_cn, 10))
        self.msg.pack(side="left")

        # 检查更新：排在「恢复出厂」左边。它天天都可能点，位置要顺手；
        # 但也不是保存类操作，所以留在左半边，跟右侧的「保 存」分开。
        # 自动检查要是已经发现新版本，就把版本号直接写在按钮上 ——
        # 用户不必点进去才知道有新版。
        pending = getattr(self.app, "new_version", "")
        base_fg = pal["seal"] if pending else pal["ink_soft"]
        base_font = ((self.app.fam_cn, 11, "bold") if pending
                     else (self.app.fam_cn, 11))
        upd = tk.Label(bar, text=("发现新版本 v" + pending) if pending else "检查更新",
                       bg=pal["paper"], fg=base_fg, font=base_font,
                       cursor="hand2", padx=12, pady=6)
        upd.pack(side="left", padx=(6, 0))
        upd.bind("<Button-1>", lambda e: self._check_update())
        upd.bind("<Enter>", lambda e: upd.configure(fg=pal["seal"]))
        # 离开时要回到它本来的颜色，不能一律写成灰的 ——
        # 有新版提示时它本来就是朱砂色，写死灰色会让提示凭空消失。
        upd.bind("<Leave>", lambda e: upd.configure(fg=base_fg))
        self.lbl_update = upd

        # 恢复出厂：和「取 消」同一套做法（tk.Label + bind），不引入新样式，
        # 也不加 ttk —— 面板里所有按钮都是自绘的，混进来会显得格格不入。
        # 放左边而不是挨着「保 存」：它是个危险动作，不该出现在手指习惯落点上。
        reset = tk.Label(bar, text="恢复出厂", bg=pal["paper"], fg=pal["ink_soft"],
                         font=(self.app.fam_cn, 11), cursor="hand2", padx=12, pady=6)
        reset.pack(side="left", padx=(6, 0))
        reset.bind("<Button-1>", lambda e: self._factory_reset())
        reset.bind("<Enter>", lambda e: reset.configure(fg=pal["seal"]))
        reset.bind("<Leave>", lambda e: reset.configure(fg=pal["ink_soft"]))

        cancel = tk.Label(bar, text="取 消", bg=pal["paper"], fg=pal["ink_soft"],
                          font=(self.app.fam_cn, 11), cursor="hand2", padx=16, pady=6)
        cancel.pack(side="right")
        cancel.bind("<Button-1>", lambda e: self.close())
        cancel.bind("<Enter>", lambda e: cancel.configure(fg=pal["seal"]))

        save = tk.Label(bar, text="保 存", bg=pal["seal"], fg="#FFF8EC",
                        font=(self.app.fam_cn, 11, "bold"), cursor="hand2", padx=22, pady=6)
        save.pack(side="right", padx=(0, 10))
        save.bind("<Button-1>", lambda e: self.save())
        save.bind("<Enter>", lambda e: save.configure(bg=pal["ink"]))
        save.bind("<Leave>", lambda e: save.configure(bg=pal["seal"]))

    # ---- 颜色规则行 ----

    def _add_row(self, days, color, bg):
        pal = self.pal
        row = tk.Frame(self.rules, bg=pal["paper"])
        row.pack(fill="x", pady=3)

        tk.Label(row, text="剩余 ≤", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left")

        days_var = tk.StringVar(value=("%g" % float(days)) if days is not None else "1")
        ent = tk.Entry(row, textvariable=days_var, width=5, justify="center",
                       font=(self.app.fam_num, 11, "bold"),
                       bg="#FFFBF2", fg=pal["ink"], relief="flat", insertbackground=pal["seal"],
                       highlightthickness=1, highlightbackground=pal["border_soft"],
                       highlightcolor=pal["seal"])
        ent.pack(side="left", padx=5, ipady=3)

        tk.Label(row, text="天", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left")

        tk.Label(row, text="字色", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left", padx=(16, 4))

        record = {"days": days_var, "color": color or "#3A322A",
                  "bg": bg, "widgets": []}

        fg_btn = self._swatch(row, record, "color")
        fg_btn.pack(side="left")

        tk.Label(row, text="底色", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(self.app.fam_cn, 10)).pack(side="left", padx=(12, 4))

        bg_btn = self._swatch(row, record, "bg")
        bg_btn.pack(side="left")

        rm = tk.Label(row, text="✕", bg=pal["paper"], fg=pal["border_soft"],
                      font=("Segoe UI", 10), cursor="hand2", padx=8)
        rm.pack(side="right")
        rm.bind("<Button-1>", lambda e: self._remove_row(record))
        rm.bind("<Enter>", lambda e: rm.configure(fg=pal["seal"]))
        rm.bind("<Leave>", lambda e: rm.configure(fg=pal["border_soft"]))

        record["row"] = row
        self.rows.append(record)

    def _swatch(self, parent, record, key):
        """一个可点击的色块按钮；点击弹出预设色板。"""
        btn = tk.Label(parent, bg=record.get(key) or self.pal["paper"], width=3,
                       relief="flat", bd=0, cursor="hand2", text=" ",
                       highlightthickness=1,
                       highlightbackground=self.pal["border_soft"],
                       highlightcolor=self.pal["seal"])
        btn.configure(font=(self.app.fam_cn, 8))
        if not record.get(key):
            btn.configure(bg=self.pal["paper"], text="自", fg=self.pal["ink_soft"])
        btn.bind("<Button-1>", lambda e: self._open_palette(btn, record, key))
        record["widgets"].append((key, btn))
        return btn

    def _refresh_swatches(self, record):
        for key, btn in record["widgets"]:
            val = record.get(key)
            if val:
                btn.configure(bg=val, text=" ")
            else:
                btn.configure(bg=self.pal["paper"], text="自")

    def _remove_row(self, record):
        if record in self.rows:
            self.rows.remove(record)
        record["row"].destroy()

    def _dismiss_palette(self, pop):
        """安全关闭色板弹窗（可能已被销毁，或被 FocusOut 重复触发）。"""
        try:
            pop.unbind("<FocusOut>")
        except tk.TclError:
            pass
        try:
            pop.destroy()
        except tk.TclError:
            pass
        self._color_popup = None
        self._color_popup_for = None

    def _open_palette(self, anchor, record, key):
        token = (id(record), key)
        if self._color_popup is not None:
            same = (self._color_popup_for == token)
            self._dismiss_palette(self._color_popup)
            if same:
                return                      # 再次点击同一个色块 = 收起

        pop = tk.Toplevel(self.win)
        pop.overrideredirect(True)
        pop.attributes("-topmost", True)
        pop.configure(bg=self.pal["border"])
        self._color_popup = pop
        self._color_popup_for = token
        inner = tk.Frame(pop, bg=self.pal["paper"])
        inner.pack(padx=2, pady=2)

        tk.Label(inner, text="  选择颜色", bg=self.pal["paper"], fg=self.pal["ink_soft"],
                 font=(self.app.fam_cn, 9), anchor="w").grid(
            row=0, column=0, columnspan=6, sticky="we", pady=(3, 4))

        def choose(value):
            record[key] = value
            self._refresh_swatches(record)
            self._dismiss_palette(pop)

        for idx, (name, hexv) in enumerate(PRESET_COLORS):
            cell = tk.Label(inner, bg=hexv, width=3, height=1, relief="solid", bd=1,
                            cursor="hand2")
            cell.grid(row=1 + idx // 6, column=idx % 6, padx=3, pady=2)
            cell.bind("<Button-1>", lambda e, v=hexv: choose(v))
            cell.bind("<Enter>", lambda e, c=cell: c.configure(bd=2))
            cell.bind("<Leave>", lambda e, c=cell: c.configure(bd=1))

        use_bg = tk.Label(inner, text="  使用当前底色（不覆盖）", bg=self.pal["paper"],
                          fg=self.pal["border"], font=(self.app.fam_cn, 9),
                          cursor="hand2", anchor="w")
        use_bg.grid(row=1 + (len(PRESET_COLORS) + 5) // 6, column=0, columnspan=6,
                    sticky="we", pady=(6, 4))
        use_bg.bind("<Button-1>", lambda e: choose(None))

        pop.update_idletasks()
        px = anchor.winfo_rootx()
        py = anchor.winfo_rooty() + anchor.winfo_height() + 2
        sw, sh = pop.winfo_screenwidth(), pop.winfo_screenheight()
        if px + pop.winfo_width() > sw:
            px = sw - pop.winfo_width() - 8
        if py + pop.winfo_height() > sh:
            py = anchor.winfo_rooty() - pop.winfo_height() - 2
        set_window_pos(pop, px, py)
        pop.bind("<FocusOut>", lambda e: self._dismiss_palette(pop))

    # ---- 逻辑 ----

    def _preview(self):
        text = self.entry.get()
        parsed, err = parse_target(text)
        if parsed is None:
            self.preview.configure(text="✕　" + (err or "格式不正确"), fg=self.pal["seal"])
            return
        delta = (parsed - datetime.datetime.now()).total_seconds()
        msg = "✓　%s　（%s，剩余 %s）" % (
            pretty_target(parsed),
            parsed.strftime("%Y-%m-%d %H:%M"),
            _human_delta(delta))
        # 末尾那段若是个「像最近几年的四位数」，它会被按时:分读掉（2026 → 20:26）。
        # 这里多嘴一句：真想写年份的人多半是把位置放错了，
        # 光看 ✓ 那一行未必反应得过来。
        toks = re.findall(r"\d+", text)
        slot = 3 if toks and len(toks[0]) == 4 else 2
        if len(toks) > slot and looks_like_recent_year(toks[slot]):
            msg += "　——「%s」被当成了时分；要写年份请放在最前面，如 %s.10.1" % (
                toks[slot], toks[slot])
        self.preview.configure(text=msg, fg="#4F7A52")

    def _collect(self):
        out = []
        for rec in self.rows:
            raw = rec["days"].get().strip()
            try:
                days = float(raw)
            except ValueError:
                return None, "「剩余 ≤」一栏需要填写数字"
            if days < 0:
                return None, "天数不能为负数"
            out.append({
                "days": days,
                "color": rec.get("color") or "#3A322A",
                "bg": rec.get("bg"),
                "label": _auto_label(days),
            })
        return out, None

    def save(self, then_export=False):
        """
        保存。

        then_export=True 时走「先存再导出」：面板上的「导出共用设置」用它 ——
        导出的必须是用户眼前这一份设置，而不是上次存过的旧值，所以先走一遍
        保存（校验、落盘、界面刷新全都照旧），成功了接着弹保存对话框。
        校验没过时照旧把原因写在面板底部，什么都不会导出。
        """
        thresholds, err = self._collect()
        if err:
            self.msg.configure(text=err)
            return

        # 地址形状现在就把关。等发信时才失败，用户看到的是一句英文或凭空断连，
        # 完全联想不到是自己少打了一个点。空着不算错，只是还没填。
        sender = self.entry_user.get().strip()
        rcpt = self.entry_to.get().strip()
        if sender and not looks_like_mail(sender):
            self.msg.configure(text="发件邮箱「%s」看着不完整，是不是少写了一个点" % sender)
            return
        if rcpt and not looks_like_mail(rcpt):
            self.msg.configure(text="收件邮箱「%s」看着不完整，是不是少写了一个点" % rcpt)
            return

        # 只在真的启用了提醒时才要求填齐邮箱，否则用户想关掉还得先补资料
        if self.var_notify.get():
            if not sender:
                self.msg.configure(text="启用了邮件提醒，请先填写发件邮箱")
                return
            if not self.entry_pass.get().strip():
                self.msg.configure(text="启用了邮件提醒，请先填写授权码")
                return

        pair, err = self._collect_notify()
        if err:
            self.msg.configure(text=err)
            return
        notify_cfg, secret = pair

        # 自动检查开关不动 apply_settings 的签名（那会牵动一圈调用点），
        # 直接改在 cfg 上 —— apply_settings 末尾本来就会 save_config 落盘。
        self.app.cfg["auto_update_check"] = bool(self.var_autoupd.get())

        err = self.app.apply_settings(self.entry.get(), thresholds,
                                      self.var_lock.get(), self.var_top.get(),
                                      self.var_autostart.get(),
                                      notify_cfg, secret)
        if err:
            self.msg.configure(text=err)
            return
        if then_export:
            self._export_shared()
            return
        self.close()

    def _export_shared(self):
        """
        导出共用设置（面板上那个按钮的落地动作）—— 分两步走。

        先弹一个小窗挑「带哪几项」，挑完才选路径写文件。中间那一步不是
        多余：用户手上是十几台机器，绝大多数设置想配成一样，可目标时刻
        每台都不同。挑一次只要几秒，事后发现时刻被冲掉了要重配十台。

        调用它的入口已经先保存过了，所以拿到的 cfg 与 secret 都是最新的。
        """
        self._picker = ExportPicker(self.app, self._write_shared)

    def _write_shared(self, selection):
        """挑完之后的落地动作：选路径 → 写文件 → 把接下来该干什么讲清楚。"""
        path = filedialog.asksaveasfilename(
            parent=self.win, title="导出共用设置",
            initialfile=SHARED_FILE, defaultextension=".json",
            initialdir=self._home_dir(),
            filetypes=[("设置文件", "*.json"), ("全部文件", "*.*")])
        if not path:
            return                       # 用户取消了，面板留着不动
        ok, why = export_shared_config(path, self.app.cfg, self.app.secret,
                                       selection)
        self.close()
        if not ok:
            messagebox.showerror("导出失败", "文件没能写出来：\n%s" % why)
            return
        names = "、".join(it["label"] for it in SHARED_ITEMS
                          if selection.get(it["key"]))
        left = "、".join(it["label"] for it in SHARED_ITEMS
                         if not selection.get(it["key"])) or "（无）"
        messagebox.showinfo(
            "已导出",
            "设置已导出到：\n%s\n\n"
            "这一份里带了：%s\n"
            "没带的（对方机器上原样保留）：%s\n\n"
            "接下来：把这份文件拷到别的机器上（U 盘、共享都行），在那台机器的\n"
            "设置面板里点「从文件导入…」选中它，设置当场就换过去了。\n\n"
            "· 本机抬头、开机自启不在文件里，每台机器各自设。\n"
            "· 文件里可能有你的邮箱授权码，是明文：别放进公共网盘、别发到群里。\n"
            "· 这份文件不会被删 —— 它就是母本，留着以后接着用。"
            % (path, names, left))

    def _import_shared(self):
        """从文件导入设置（不删文件 —— 这是用户自己挑的那份，可能是母本）。"""
        path = filedialog.askopenfilename(
            parent=self.win, title="选择共用设置文件",
            initialdir=self._home_dir(),
            filetypes=[("设置文件", "*.json"), ("全部文件", "*.*")])
        if not path:
            return
        err = self.app.import_shared_from(path)
        if err:
            messagebox.showerror("导入失败", err)
            return
        self.close()
        messagebox.showinfo("已导入",
                            "设置已经读进来，界面也按新设置刷新了。\n\n"
                            "文件里没有的项本机保持原样：抬头、开机自启，"
                            "以及导出时没勾上的那些。")

    def _home_dir(self):
        """对话框的起始目录：优先桌面，没有就退到用户主目录。"""
        home = os.path.expanduser("~")
        desk = os.path.join(home, "Desktop")
        return desk if os.path.isdir(desk) else home

    def _factory_reset(self):
        """
        点「恢复出厂」：先把后果用人话讲清楚，确认后才动手。

        必须二次确认 —— 这一步会把授权码一起清掉，而授权码是用户去邮箱后台
        单独申请来的（不是登录密码），丢了他得重新走一遍申请流程。
        所以提示里要把「会失去什么」逐条列出来，不能只写一句「确定吗」。

        确认后不做任何「自己写默认值回去」的动作：数据键删掉就是删掉，
        界面由 app.factory_reset 当场重画，用户不需要重启程序。
        """
        ok = messagebox.askyesno(
            "恢复出厂设置",
            "将清空本程序保存的全部数据，恢复成刚安装时的样子：\n\n"
            "　· 目标时刻\n"
            "　· 颜色规则与配色\n"
            "　· 邮箱地址与授权码\n"
            "　· 寄信履历\n"
            "　· 窗口位置与大小\n\n"
            "清空后无法撤销（授权码需要重新去邮箱申请）。\n"
            "开机自动运行的设置会保留，不受影响。\n\n"
            "是否继续？",
            parent=self.win)
        if not ok:
            return

        err = self.app.factory_reset()
        if err:
            self.msg.configure(text=err)
            return
        self.close()
        messagebox.showinfo(
            "恢复出厂设置",
            "已恢复出厂设置。\n\n"
            "目标时刻已改回示例值，重新点「設」即可设置自己的日子。\n"
            "（要送人或卸载：再取消勾选「开机自动运行」，退出程序后删掉 exe 就行。）",
            parent=self.app.root)

    # ---- 在线升级 ----
    #
    # 联网一律走后台线程，结果再切回界面线程显示。Tk 的对象只能在主线程碰，
    # 工作线程里直接改 Label 会随机崩，所以统一经 _update_ui 中转。

    def _update_ui(self, fn):
        """把一段界面操作排到主线程去执行。"""
        try:
            self.win.after(0, fn)
        except tk.TclError:
            pass

    def _update_thread(self, worker):
        import threading
        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def _check_update(self):
        if self._updating:
            return
        self._updating = True
        self.msg.configure(text="正在检查新版本…", fg=self.pal["ink_soft"])
        self._update_thread(self._update_query)

    def _update_query(self):
        info, err = fetch_update_info()
        if err or not info:
            self._update_ui(
                lambda m=err: self._update_stop("检查更新失败：" + str(m),
                                                self.pal["seal"]))
            return
        if not update_available(info.get("version")):
            # 手动查到「已是最新」，顺手把右上角那颗小红点灭掉。
            # 必须经 _update_ui 回主线程 —— 这里跑在后台线程上，直接碰 canvas 会崩。
            self._update_ui(lambda: self.app.set_new_version(""))
            self._update_ui(
                lambda: self._update_stop("已是最新版本 v" + APP_VERSION, "#4F7A52"))
            return
        self._update_ui(lambda: self.app.set_new_version(info.get("version")))
        self._update_ui(lambda i=info: self._update_ask(i))

    def _update_stop(self, text, color):
        self._updating = False
        self.msg.configure(text=text, fg=color)

    def _update_ask(self, info):
        """
        第一次确认：有没有新版、改了什么，说清楚再问要不要下。

        用户明确要求「二次确认」，所以这里只问下载，不擅自开始。
        """
        notes = (info.get("notes") or "").strip()
        if len(notes) > 400:
            notes = notes[:400] + "…"
        size_mb = (info.get("size") or 0) / 1048576.0
        ok = messagebox.askyesno(
            "发现新版本 v%s" % info.get("version", "?"),
            "当前版本：v%s\n"
            "新版本　：v%s（来自 %s）\n"
            "下载大小：约 %.1f MB\n\n"
            "更新内容：\n%s\n\n"
            "现在下载并更新吗？\n"
            "你的目标时刻、颜色规则、邮箱设置都不受影响，"
            "更新完成后程序会自动重启一次。"
            % (APP_VERSION, info.get("version", "?"),
               info.get("source") or "网络", size_mb,
               notes or "　（作者这次没写说明）"),
            parent=self.win)
        if not ok:
            self._update_stop("已取消，仍是 v" + APP_VERSION, self.pal["ink_soft"])
            return
        self.msg.configure(text="正在下载…", fg=self.pal["ink_soft"])
        self._update_thread(lambda: self._update_download(info))

    def _update_download(self, info):
        import tempfile

        last = [0.0]

        def prog(got, total):
            # 下载每 64KB 回调一次，全量刷界面会把主线程拖死，节流到 0.3 秒一报
            now = time.time()
            if now - last[0] < 0.3 and (total < 0 or got < total):
                return
            last[0] = now
            if total > 0:
                text = "正在下载… %.1f / %.1f MB" % (got / 1048576.0,
                                                     total / 1048576.0)
            else:
                text = "正在下载… %.1f MB" % (got / 1048576.0)
            self._update_ui(
                lambda t=text: self.msg.configure(text=t,
                                                  fg=self.pal["ink_soft"]))

        zip_path, err = download_update(info, progress=prog)
        if not zip_path:
            self._update_ui(lambda m=err: self._update_stop(
                str(m or "下载失败"), self.pal["seal"]))
            return

        workdir = tempfile.mkdtemp(prefix="anc_upd_x_")
        exe, err = extract_exe(zip_path, workdir)
        if not exe:
            self._update_ui(lambda m=err: self._update_stop(
                str(m or "解压失败"), self.pal["seal"]))
            return
        self._update_ui(lambda i=info, e=exe: self._update_ready(i, e))

    def _update_ready(self, info, exe):
        """第二次确认：包已经下好且校验通过，问现在换不换。"""
        ok = messagebox.askyesno(
            "更新已就绪",
            "新版本 v%s 已下载并通过校验。\n\n"
            "现在关闭程序、切换到新版本吗？\n\n"
            "（程序会自动重新打开。旧版本会留一个 .old 文件在旁边，"
            "新版连续正常启动几回之后才会自动清掉它 —— "
            "在那之前把 .old 改回 .exe 就能退回现在这个版本。）"
            % info.get("version", "?"),
            parent=self.win)
        if not ok:
            self._update_stop("已下载，等你决定何时重启", self.pal["ink_soft"])
            return

        ok2, err = install_update(exe)
        if not ok2:
            self._update_stop(str(err or "更新失败"), self.pal["seal"])
            return

        # 新版本已经在路上了，旧进程功成身退。
        # 用 os._exit 而不是 sys.exit：此刻 tkinter 主循环还在跑，
        # sys.exit 抛出的异常会被循环吞掉，程序退不干净。
        try:
            self.app._settings = None
            self.win.destroy()
        except Exception:
            pass
        os._exit(0)

    def close(self):
        # 滚轮是 bind_all 挂上去的（面板里所有控件都能滚），关窗必须解绑，
        # 否则这扇窗没了，滚轮事件还在往一个已销毁的 canvas 上送。
        try:
            self.win.unbind_all("<MouseWheel>")
        except tk.TclError:
            pass
        if self._color_popup is not None:
            self._dismiss_palette(self._color_popup)
        # 挑选项的小窗还开着的话一起关掉 —— 面板没了它留着，会变成一扇
        # 点什么都回不去的孤儿窗（它的回调还要往已销毁的面板上挂对话框）。
        picker = getattr(self, "_picker", None)
        if picker is not None:
            self._picker = None
            try:
                picker.close()
            except Exception:
                pass
        self.app._settings = None
        try:
            self.win.destroy()
        except tk.TclError:
            pass

    # ---- 杂项 ----

    def _center(self):
        sw = self.win.winfo_screenwidth()
        sh = self.win.winfo_screenheight()
        w = max(self.W, self.win.winfo_reqwidth())
        h = self.win.winfo_reqheight()
        # 加了传书区之后面板变得挺高。小屏笔记本放不下时贴着顶部显示，
        # 至少保证标题栏能够得着 —— 否则用户连关都关不掉。
        top = max(8, min((sh - h) // 2 - 40, sh - h - 16))
        set_geometry(self.win, w, h, (sw - w) // 2, top)

    def _drag_bind(self, widget):
        widget.bind("<Button-1>", self._drag_start)
        widget.bind("<B1-Motion>", self._drag_move)

    def _drag_start(self, event):
        self._pt = (event.x_root - self.win.winfo_x(), event.y_root - self.win.winfo_y())

    def _drag_move(self, event):
        if not hasattr(self, "_pt"):
            return
        # 拖到左屏 / 上屏时坐标是负的，必须走 set_window_pos，否则窗口会「拖不动」
        set_window_pos(self.win, event.x_root - self._pt[0],
                       event.y_root - self._pt[1])


def _auto_label(days):
    if days >= 1:
        return "剩余 %g 日内" % days
    hours = days * 24
    if hours >= 1:
        return "最后 %g 小时" % round(hours)
    return "最后 %g 分钟" % round(days * 1440)


def _human_delta(seconds):
    if seconds <= 0:
        return "已到时刻"
    d = int(seconds // 86400)
    h = int(seconds % 86400 // 3600)
    m = int(seconds % 3600 // 60)
    s = int(seconds % 60)
    parts = []
    if d:
        parts.append("%d 天" % d)
    if h or d:
        parts.append("%d 时" % h)
    if m or h or d:
        parts.append("%d 分" % m)
    parts.append("%d 秒" % s)
    return "".join(parts)


# --------------------------------------------------------------------------

CRASH_LOG_FILE = "ac_crash.log"


def install_crash_hook():
    """
    打包成 windowed exe 后没有控制台，未捕获异常只能弹一个 PyInstaller
    的 Error 框， traceback 随风而去 —— 用户看到框，我们什么都看不到。
    装上这个钩子后，异常照常弹框，但在此之前会先写一份完整 traceback
    到 %TEMP%\\ac_crash.log（追加模式），事后能查、能贴、能诊断。
    """
    import tempfile
    import traceback

    prev = sys.excepthook

    def hook(tp, val, tb):
        try:
            with open(os.path.join(tempfile.gettempdir(), CRASH_LOG_FILE),
                      "a", encoding="utf-8") as f:
                f.write("=== %s ===\n" % time.strftime("%Y-%m-%d %H:%M:%S"))
                traceback.print_exception(tp, val, tb, file=f)
                f.write("\n")
        except Exception:
            pass
        if prev:
            try:
                prev(tp, val, tb)
            except Exception:
                pass

    sys.excepthook = hook


def main():
    install_crash_hook()   # 越早越好：之后任何未捕获异常都会留诊断文件

    # 打包成 exe 之后，同一个 exe 兼任两个角色：
    #   双击           -> 正常显示倒计时窗口
    #   exe mailer ... -> 当发信脚本跑，发完即退（见 run_mailer_cli）
    # 判据放在取锁之前：发信进程不该被单实例锁挡住。
    if len(sys.argv) > 1 and sys.argv[1] == "mailer":
        return run_mailer_cli(sys.argv[1:])
    if len(sys.argv) > 1 and sys.argv[1] == "selfupdate":
        return run_selfupdate_cli()

    after_update = AFTER_UPDATE_ARG in sys.argv

    if not acquire_single_instance():
        # 更新后的那次重启特殊处理：旧进程把我们拉起来之后才退出，
        # 它手里的互斥体还没交出来。这时若照老规矩「唤醒它再自己退出」，
        # 被唤醒的那个马上就死了，结果就是程序消失。所以改成等锁。
        if after_update and wait_for_instance_lock():
            pass
        else:
            # 已经有实例在跑：不再开新进程（每个进程要占几十 MB），
            # 而是让已有窗口显出来——用户双击就是想看见它
            request_wake()
            return
    clear_wake_file()
    # 旧 exe（.old）不在这儿清了：它现在是「新版本连续稳定启动满几次」才删，
    # 触发点挂在窗口起来 60 秒之后（见 note_successful_run / _note_run_ok）。
    migrate_legacy_files()   # 老版本的配置/凭据/履历文件搬进注册表（一次性）
    # 这里曾经会在启动时扫 exe 旁边有没有共用设置文件、有就读走并删掉
    # （v1.6 起去掉了 —— 见 apply_shared_file 的说明）。现在导入只走设置面板
    # 那条路：什么时候导、导哪一份，都由用户当场挑，程序不擅自改设置。
    app = CountdownApp()
    app.run()


if __name__ == "__main__":
    sys.exit(main())
