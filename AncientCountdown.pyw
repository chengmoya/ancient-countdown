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
APP_VERSION = "1.10"

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

# ---- 数据仓：用户目录下的一个配置文件 ----
#
# 全部数据装在 %USERPROFILE%\.古风倒计时\设置.json 这一个文件里：
# 目标时刻、配色、邮箱凭据、寄信履历、盯守与关机的状态。
#
# 为什么从注册表搬出来：
#   · 注册表藏在系统深处，用户看不见、改不了、也没法拷到别的机器；
#   · 备份/换机时无从下手，出问题只能 regedit；
#   · exe 若被放在 Program Files 这类位置，普通用户没有写权限。
# 代价是邮箱授权码从「藏在系统里」变成「文件里的一段」——
# 所以它单独加密（见 seal_text），拷到别的机器上自动失效。
DATA_DIR_NAME = ".古风倒计时"     # 用户目录下那个文件夹（带点 = 平时不碍眼）
DATA_FILE = "设置.json"           # 唯一的持久文件
DATA_FORMAT = 1                   # 文件格式版本，将来若改结构靠它认

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
# 只是一次减法，连存储都不用读。
UPDATE_CHECK_KEY = "update_check"        # 自动检查的状态（v1.8 起存数据文件）
UPDATE_AUTO_START_DELAY = 60             # 启动后静置多少秒才开始自动检查
UPDATE_AUTO_SCAN_SEC = 6 * 3600          # 巡检间隔：每 6 小时醒一次看看该不该查
UPDATE_CHECK_MIN_GAP = 7 * 86400         # 两次真查询之间至少隔 7 天

# ---- 更新后的「可回滚窗口」----
#
# .old 是用户唯一的回滚手段，所以不能新版本一启动就删：
# 用户说的「新版有问题」往往不是「起不来」（起不来时这段代码根本跑不到），
# 而是「起来了但功能不对」—— 那种情况下 .old 要是已经没了，想退都退不回去。
UPDATE_GUARD_KEY = "update_guard"        # 更新后的成功启动计数（v1.8 起存数据文件）
UPDATE_GUARD_RUNS = 3                    # 稳定启动满几次才把 .old 删掉
UPDATE_GUARD_DELAY_MS = 60 * 1000        # 启动后满多久才算「这一次启动成功了」

# ---- 定时关机 · 取日期 / 到点执行 ----
#
# 场景：机器上挂着游戏，什么时候收工不取决于人，而取决于用户自己网站上
# 那一串日期数字（他那边随时会改）。所以那个网址是时间的权威来源，
# 程序只负责把它取回来、解析成时刻、到点把机器关掉。
#
# 第二个来源是**倒计时目标本身**：本机自己设的日子到了也关（from_target）。
# 两个来源各算各的时刻，**谁先到谁关**；到点之后先弹窗问一句，没人理才真关。
#
# 为什么不用 Windows 自带的「计划任务」那条路：网站的日期随时会变，
# 变了就得重排一次计划；程序自己倒计时、自己到点动手，改一次网址就行。
SITE_STATE_KEY = "site_date"             # 最近一次取回的结果（给人看的）
SHUTDOWN_STATE_KEY = "shutdown_state"    # 关机是否已经触发 / 已错过
SITE_FETCH_TIMEOUT = 12                  # 取一次最多等几秒
SITE_FETCH_START_DELAY = 20              # 启动后静置多少秒才去取第一次
SITE_MAX_BYTES = 64 * 1024               # 日期数字不可能超过这个数，防异常响应
SITE_RAW_KEEP = 400                      # 原文只留这么多字给人核对
SHUTDOWN_GRACE_DEFAULT = 60              # 确认窗等你多少秒（不点就执行）
SHUTDOWN_GRACE_MAX = 600                 # 最长十分钟 —— 再长就不叫「到点关机」了
SHUTDOWN_RETRY_SEC = 60                  # 命令发出去了机器却没关成，隔多久再试一次
# 关机时刻的两个来源。两个都算数时取**先到的那个**：
#   remote  从用户自己的网址取回来的时刻
#   target  用户自己设的倒计时目标（归零那一刻）
# 为什么保留两个：网址那个是「那边说了算」的收工时间；倒计时那个是
# 「我这台机器自己该关的时候」。谁先到谁关，才符合两边各自的用途。
SHUTDOWN_SOURCES = (("remote", "网址取回"),
                    ("target", "倒计时目标"))

# ---- 窗口盯守 ----
#
# 场景：无人值守的机器上挂着游戏，万一游戏窗口没了（掉线、崩了、被谁关了），
# 得有人知道。做法是定时看一眼那扇窗还在不在。
#
# 三条要紧的规矩：
#   · **必须先看见过它**，之后不见了才算「消失」。机器刚开机、游戏还没起来时
#     一直看不见它，那时候发信是纯骚扰。
#   · **机器重启过就推回「等出现」**（_disarm_watch_after_reboot 比开机时刻）。
#     状态存在数据文件里，不推倒的话每次开机都会白寄一封信。
#   · 消失之后**不立刻发信**，先弹一扇窗问一句「是你自己关的吗」，同时
#     **继续核实**（每 30 秒一次）：倒计时的每一分钟都要求它确实还不在，
#     这中间它只要又出现过一次就当场撤销。无人应答时倒计时走完照样把信
#     寄出去 —— 默认是「寄」，不确认就等于「我不知道，按最坏情况处理」。
WATCH_STATE_KEY = "watch_state"          # 盯守状态机（存数据文件，重启后接着盯）
ALERT_STATE_KEY = "alert_state"          # 盯守通知的寄信记录
WATCH_PROBE_MIN = 1                      # 巡检间隔的下限（分钟）
WATCH_PROBE_MAX = 1440                   # 上限一天 —— 比这更稀就不叫盯守了
WATCH_GRACE_MIN = 1                      # 「连续不见多少分钟才寄信」的下限（分钟）
WATCH_GRACE_MAX = 1440                   # 上限一天 —— 比这更长就不叫告警了
WATCH_CONFIRM_SEC = 30                   # 问话期间每隔多少秒核实一次窗口在不在
                                         # （「持续不在线 N 分钟才寄信」的落地：
                                         #  这 N 分钟里它只要又出现过一次就撤销）
WATCH_BOOT_DRIFT_SEC = 120               # 比对「开机时刻」时的容差（秒）。
                                         # 墙上时钟被 NTP 调过几分钟也算「重启过」——
                                         # 那是往安全的方向错：最多晚一会儿寄信，
                                         # 不会白寄（见 _disarm_watch_after_reboot）。
WINDOW_LIST_MAX = 120                    # 下拉框最多列这么多扇窗，防菜单长到屏幕外
WATCH_DRILL_SEC = 60                     # 「演练」时问话窗等多少秒就自动寄信
                                         # （真实盯守按 grace_min 分钟；演练是当场看
                                         # 效果，让用户等十分钟就没人肯试了）

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
    # 设置面板自己的尺寸（**和上面那个「主窗口」是两回事，别混**）。
    # 0 = 还没调过，按内容与屏幕算一个默认值。
    # 为什么不塞进 config.window：那一段是「跨机器同步」的一项，各机器屏幕
    # 大小不同，把面板尺寸带过去会让小屏机器上的面板直接顶出屏幕。
    # 这个段不在 SHARED_ITEMS 里，导出共用设置与远程同步都不会碰它。
    "panel": {"w": 0, "h": 0},

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

    # 定时关机：两个时刻来源，**谁先到谁关**。
    #   remote  你那个网址上的一串日期数字，取回来的那一刻就是关机时刻
    #   target  上面那个倒计时目标，归零那一刻也是关机时刻（from_target 控制）
    #
    # ⚠️ 两个时刻仍然是**两个各自独立的变量**，谁也不改写谁：
    #   去网址取一次数，绝不会动 cfg["target"]（v1.6 就是那么错的，用户当场指出）。
    #   现在只是「谁先到就按谁关」，不是把它们合成一个。
    #   合并的后果是：用户设的倒计时会被一次取数悄悄换掉 —— 别再退回去。
    #
    # 默认关着 —— 这是会「自己把电脑关掉」的功能，必须用户亲口说要。
    "shutdown": {
        "enabled": False,
        "from_target": True,        # 倒计时归零也关机（默认开：用户明确要的）
        "url": "",                  # 你那个网站的地址，返回一串日期数字
        "auto_fetch": True,         # 启动时自动取一次
        "refresh_hours": 6.0,       # 之后每隔几小时再取一次（0 = 不再自动取）
        "grace_sec": SHUTDOWN_GRACE_DEFAULT,   # 确认窗等你几秒
        # 关机时刻的**另一个指定来处**：设置文件里直接写死一个时刻。
        # 远程设置 / 共用设置那份文件带上这一项，各台机器取回来就是关机时刻 ——
        # 用户只维护一份配置文件（远程设置本来就会定时下载），不必再单独
        # 维护一个「返回日期数字的网址」。写法同 target（如 "2026.10.20.18.00"），
        # 留空 = 没指定；写 "" 可以撤掉。
        #
        # 它和 url 那条喂的是**同一个变量** self.shutdown_at（来源都记 "remote"）：
        #   · 运行期内谁后到谁算数（网址取到新值会当场覆盖，远程设置拉回来也会）；
        #   · 重启后以这份文件里的值为准（见 _restore_shutdown_at）——
        #     文件是用户此刻明确写下的值，site_date 只是「上次网址取到了什么」。
        # ⚠️ 它同样绝不碰 cfg["target"]：主界面那个倒计时各机器各自设，
        #    这是用户点名划的线（见自检里「主界面倒计时目标没被改掉」那几条）。
        "at": "",
    },

    # 窗口盯守：盯着某一扇窗，它不见了就寄信告诉你。
    # 同样默认关着 —— 它会弹窗、会发信，得用户自己开。
    "watch": {
        "enabled": False,
        "title": "",                # 要盯的窗口名称（关键字，短一点更稳）
        "interval_min": 30,         # 多久看一眼（分钟）
        "grace_min": 10,            # 连续不见多少分钟才寄信（期间反复核实，它一出现就撤销）
        # 「窗口下次出现时自动接着盯」是**写死的行为**，没有开关：
        # 无人值守的机器上，一次通报之后当然要接着盯，否则第二次掉线就没人知道了。
        # 落地方式见 finish_watch_alert（处理完一律退回 waiting 那一档）。
    },

    # 远程设置：从一个网址取回一份设置，一次配好十几台机器。
    # 取回来的就是「导出共用设置」那个格式 —— 同一套校验、同一套剔除规则，
    # 所以「U 盘拷一份」和「从网址拉一份」拿到的是同一种东西。
    #
    # 密码类的东西（邮箱授权码、这里的认证密码与令牌）**永远不从网上取**：
    # 取回来的内容里只有 config 那一段，凭据一概不认 —— 只在本机填。
    "remote": {
        "enabled": False,
        "url": "",
        # none = 不用认证；basic = 用户名 + 密码；bearer = 一串令牌；
        # header = 自定义请求头（各家对象存储、代码托管爱用这种）
        "auth": "basic",
        "user": "",                 # basic 的用户名（密码与头名称存在凭据里）
        "refresh_hours": 6.0,       # 每隔几小时拉一次（0 = 只在启动时拉）
        "items": {},                # 参与同步的项，{} = 用默认那套
        "last_at": "",              # 下面三个只是给人看的记录，不是设置
        "last_ok": False,
        "last_note": "",
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


APP_DIR = app_dir()          # 程序所在目录（exe 那个文件夹）


def default_data_dir():
    """
    数据默认放哪：用户目录下的一个文件夹。

    为什么不放程序所在目录（老做法）：exe 可能被搁在 Program Files
    这类普通用户没有写权限的地方，而配置是随时要写的 —— 改个窗口位置
    都会失败。用户目录永远可写。

    为什么名字带个点：Windows 上以点开头的文件夹默认不显示，
    平时翻目录不碍眼；要找的时候地址栏敲 %USERPROFILE% 就能看见。
    """
    return os.path.join(os.path.expanduser("~"), DATA_DIR_NAME)


def data_dir():
    """
    配置与状态文件的存放目录。

    设了环境变量 ANCIENT_COUNTDOWN_HOME 时改道到它 —— 这个口子留给
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
    path = default_data_dir()
    try:
        os.makedirs(path, exist_ok=True)
    except OSError:
        pass
    return path


DATA_DIR = data_dir()
DATA_PATH = os.path.join(DATA_DIR, DATA_FILE)

# 老版本把数据放在「程序旁边」的那几个 json，只用于迁移。
# 文件名是历史，别改 —— 改了就读不到别人机器上的老数据了。
# 「数据」这三个要搬进新配置；搬完就地删掉 —— 其中 notify_secret.json
# 存的是明文授权码，数据既然已经加密存好了，就不该在硬盘上再留一份明文。
LEGACY_FILE_KEYS = (
    ("countdown_config.json", "config"),
    (NOTIFY_SECRET_FILE, "notify_secret"),
    (NOTIFY_STATE_FILE, "notify_state"),
)

# 这几个是「瞬时的信箱文件」，不迁移 —— 搬一封早就过期的发信任务，
# 只会在新机器上白发一封莫名其妙的信。但收尾时照样要清掉：
# 使用者要求程序文件夹里自始至终只有 exe 一个文件。
LEGACY_JUNK_FILES = (
    NOTIFY_TASK_FILE, NOTIFY_RESULT_FILE, NOTIFY_TEST_RESULT_FILE, WAKE_FILE,
)

# 发信脚本是「程序」不是「数据」，始终跟着程序走
MAILER_PATH = os.path.join(APP_DIR, MAILER_FILE)


# --------------------------------------------------------------------------
# 数据仓 · 用户目录下的一个配置文件
#
# 配置、凭据、履历全部存进 %USERPROFILE%\.古风倒计时\设置.json，一个文件装完。
#
# 为什么不是注册表（v1.7 及以前的做法）：
#   · 注册表藏在系统深处，用户看不见、改不了、也没法拷到别的机器上；
#   · 换机器想搬走设置，注册表根本无从下手，出问题只能 regedit；
#   · exe 若被放在 Program Files 这类位置，普通用户压根没有写权限。
# 代价是邮箱授权码从「藏在系统里」变成「文件里的一段」。所以它单独加密
# （见 seal_text）—— 密钥由 Windows 按「当前机器 + 当前账号」派生，
# 文件拷到别处就是一段解不开的废字符串。
#
# 四个函数的名字与签名**刻意保持和注册表时代一模一样**：
# 调用点有五十来处，连测试代码都在用它们。换实现不换接口，一行都不用改。
# 演练隔离：设了 ANCIENT_COUNTDOWN_HOME 时数据目录整个改道，真实数据分毫不动。
# --------------------------------------------------------------------------

# 这几个是「信箱」：跨进程传递、读过就删。各自独立成一个小文件，不进主文件。
#
# 为什么非拆不可：发信是另一个进程干的（见 mailer.pyw）。若和设置共用一个
# 文件，主程序在这头写设置、发信进程在那头写结果 —— 两边都是「读全文 →
# 改一处 → 写回全文」，后写的会把先写的整段盖掉。表现是「设置改完过一会儿
# 自己变回去了」，极难查。拆开之后主文件永远只有主进程一个人写，
# 物理上不可能互相覆盖。
MAILBOX_NAMES = ("notify_task", "notify_result", "notify_test_result", "wake")

# 主文件的内存副本。只有主进程会写主文件，所以缓存绝对安全；
# 而 tick 每秒都要看一眼唤醒信号（那走信箱），每回都读盘太浪费。
_data_cache = None


def reg_store_key():
    """
    数据仓的「地址」。注册表时代返回注册表键路径，现在返回数据文件全路径 ——
    自检和日志里会打印它，方便人照着去找。
    """
    return DATA_PATH


def _data_file_read():
    """把整个数据文件读进来。不存在 / 读不动 / 内容坏，一律当空仓。"""
    try:
        with open(DATA_PATH, "r", encoding="utf-8") as fp:
            doc = json.load(fp)
    except (OSError, ValueError):
        return {}
    if not isinstance(doc, dict):
        return {}
    body = doc.get("data")
    return body if isinstance(body, dict) else {}


def _data_file_write(payload):
    """
    原子写：先写同目录的 .tmp，落盘后再改名盖过去。

    直接往目标文件上写是不行的 —— 写到一半断电或崩溃，用户手上就只剩半个
    json，下次启动什么都读不出来，配置等于全丢。先写临时文件、fsync 落盘、
    再 os.replace（同卷改名是原子操作），要么是旧的完整内容，要么是新的
    完整内容，不存在中间态。
    """
    doc = {
        "format": DATA_FORMAT,
        "app": APP_NAME,
        "note": "这是「古风倒计时」的全部数据，就这一个文件。邮箱授权码已加密。",
        "data": payload,
    }
    tmp = DATA_PATH + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as fp:
            json.dump(doc, fp, ensure_ascii=False, indent=2)
            fp.write("\n")
            fp.flush()
            os.fsync(fp.fileno())
        os.replace(tmp, DATA_PATH)
        return True, ""
    except OSError as exc:
        try:
            os.remove(tmp)
        except OSError:
            pass
        return False, str(exc)


def _cached_data():
    global _data_cache
    if _data_cache is None:
        _data_cache = _data_file_read()
    return _data_cache


def _mailbox_path(name):
    return os.path.join(DATA_DIR, name + ".json")


def reg_store_read(name, fallback):
    """读一项数据。不存在或内容损坏时返回 fallback 的深拷贝。"""
    if name in MAILBOX_NAMES:
        try:
            with open(_mailbox_path(name), "r", encoding="utf-8") as fp:
                data = json.load(fp)
        except (OSError, ValueError):
            return json.loads(json.dumps(fallback))
        if data is None:
            return json.loads(json.dumps(fallback))
        return data
    data = _cached_data().get(name)
    if data is None:
        return json.loads(json.dumps(fallback))
    return json.loads(json.dumps(data))


def reg_store_write(name, data):
    """写一项数据。返回 (是否成功, 失败说明)。"""
    if name in MAILBOX_NAMES:
        path = _mailbox_path(name)
        try:
            with open(path + ".tmp", "w", encoding="utf-8") as fp:
                json.dump(data, fp, ensure_ascii=False)
            os.replace(path + ".tmp", path)
            return True, ""
        except OSError as exc:
            return False, str(exc)

    global _data_cache
    body = dict(_cached_data())
    body[name] = data
    ok, err = _data_file_write(body)
    if ok:
        _data_cache = body
    return ok, err


def reg_store_delete(name):
    """删一项数据。不存在也当删成功（幂等）。"""
    if name in MAILBOX_NAMES:
        for p in (_mailbox_path(name), _mailbox_path(name) + ".tmp"):
            try:
                os.remove(p)
            except OSError:
                pass
        return

    global _data_cache
    body = dict(_cached_data())
    if name in body:
        body.pop(name)
        if _data_file_write(body)[0]:
            _data_cache = body


def reg_store_drop_all(key_path=None):
    """
    整个清掉数据仓（恢复出厂与演练收尾用）。

    参数是历史遗留（注册表时代要传键路径），现在忽略 —— 数据只有一份。
    """
    global _data_cache
    _data_cache = {}
    for p in (DATA_PATH, DATA_PATH + ".tmp"):
        try:
            os.remove(p)
        except OSError:
            pass
    for name in MAILBOX_NAMES:
        reg_store_delete(name)


# ---- 授权码加密 ----
#
# 用 Windows 自带的 DPAPI：密钥由系统按「当前机器 + 当前 Windows 账号」派生，
# 我们既不生成也不保管任何密钥，零第三方依赖。
#
# 直接效果：把 设置.json 拷到另一台机器（或换一个 Windows 账号）下，
# 密码那段解不开，程序当作空的 —— 用户在设置面板重填一次即可。
# 这正是「每台机器自己填密码」想要的样子。
#
# 加解密失败一律退回明文：宁可弱一点，也不能因为加不了密让密码彻底用不了。
_SEAL_PREFIX = "dpapi:"
_CRYPTPROTECT_UI_FORBIDDEN = 0x01


def _dpapi(data, unprotect):
    """调 CryptProtectData / CryptUnprotectData。返回 bytes，失败抛异常。"""
    import ctypes
    import ctypes.wintypes

    class Blob(ctypes.Structure):
        _fields_ = [("cbData", ctypes.wintypes.DWORD),
                    ("pbData", ctypes.POINTER(ctypes.c_char))]

    crypt32 = ctypes.WinDLL("crypt32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    src_buf = ctypes.create_string_buffer(data, len(data))
    src = Blob(len(data), ctypes.cast(src_buf, ctypes.POINTER(ctypes.c_char)))
    dst = Blob()

    fn = crypt32.CryptUnprotectData if unprotect else crypt32.CryptProtectData
    # 两个函数的参数表一样长：Protect(pDataIn, szDataDescr, pEntropy,
    # pvReserved, pPrompt, dwFlags, pDataOut)，Unprotect 的第二个参数是个
    # 出参指针，传 None 即可。dwFlags 带 UI_FORBIDDEN —— 无人值守的机器上
    # 绝不能弹任何系统对话框。
    if not fn(ctypes.byref(src), None, None, None, None,
              _CRYPTPROTECT_UI_FORBIDDEN, ctypes.byref(dst)):
        raise OSError(ctypes.get_last_error(), "系统加密接口调用失败")
    try:
        return ctypes.string_at(dst.pbData, dst.cbData)
    finally:
        kernel32.LocalFree(dst.pbData)


def seal_text(text):
    """加密一段文字。加不了就原样返回 —— 绝不因为加不了密让密码用不成。"""
    text = text or ""
    if not text:
        return ""
    try:
        import base64
        return _SEAL_PREFIX + base64.b64encode(
            _dpapi(text.encode("utf-8"), unprotect=False)).decode("ascii")
    except Exception:                             # noqa: BLE001
        return text


def unseal_text(text):
    """解开 seal_text 加密的东西。解不开返回空串（多半是别台机器拷来的）。"""
    text = text or ""
    if not text.startswith(_SEAL_PREFIX):
        return text        # 老数据或手工填的明文，原样用
    try:
        import base64
        blob = base64.b64decode(text[len(_SEAL_PREFIX):])
        return _dpapi(blob, unprotect=True).decode("utf-8")
    except Exception:                             # noqa: BLE001
        return ""


# ---- 老数据迁移 ----
#
# 两种老形态都要照顾：
#   · 更早的版本（v1.4 及以前）把数据放在程序旁边的 json 文件里；
#   · v1.5–v1.7 把数据放在注册表 HKCU\Software\AncientCountdown 里。
#
# 只在数据文件还不存在时搬一次。搬完**不动**老数据 —— 注册表和旧文件原样
# 留着当退路，用户确认新版没问题后可以在设置面板里自己清掉。
#
# 读与写拆开：collect_legacy_data 是纯读，自检可以喂它假的老数据来跑，
# 完全不必碰使用者机器上那份真的。
REG_STORE_ROOT = r"Software\AncientCountdown"

# 注册表里那些值名，和文件里的键名一一对应（一个都不能漏，漏了就丢数据）
REGISTRY_ITEMS = ("config", "notify_secret", "notify_state", "site_date",
                  "shutdown_state", "watch_state", "alert_state",
                  "update_check", "update_guard", "shared_last",
                  "shared_error", "shared_export_items")


def collect_registry_data(root=None):
    """把注册表里的老数据读成一份 dict。纯读，不改任何东西。"""
    root = REG_STORE_ROOT if root is None else root
    out = {}
    for name in REGISTRY_ITEMS:
        try:
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER, root, 0,
                                winreg.KEY_READ) as key:
                raw, _ = winreg.QueryValueEx(key, name)
            value = json.loads(raw)
        except (OSError, ValueError):
            continue
        if value is not None:
            out[name] = value
    return out


def collect_legacy_data(registry_root=None, folder=None):
    """
    把老版本的数据收集成新格式的一份 dict。纯读不写。

    registry_root / folder 传 None 就用真实位置；自检传别的值，
    就能拿假的老数据跑，完全不必碰使用者的真实数据。
    """
    if folder is None:
        folder = APP_DIR

    out = collect_registry_data(registry_root)

    # 更老的形态：程序旁边的 json 文件。逐项补空 —— 文件里有、注册表里
    # 没有的才用（那些年头久远，当年注册表里根本还没有）。
    for fname, key in LEGACY_FILE_KEYS:
        try:
            with open(os.path.join(folder, fname), "r", encoding="utf-8") as fp:
                value = json.load(fp)
        except (OSError, ValueError):
            continue
        if value is not None and key not in out:
            out[key] = value
    return out


def drop_legacy_files(folder=None):
    """
    清掉老版本留在程序文件夹里的那几个 json。返回删掉的文件名列表。

    只在「新数据已经落盘」之后才调用 —— 这是数据搬家，不是删档。
    注册表里的老数据**不删**：它不占地方，也不在用户眼皮底下，
    万一使用者想退回旧版本，那边还有一份完整的。
    """
    folder = APP_DIR if folder is None else folder
    dropped = []
    for fname in [n for n, _ in LEGACY_FILE_KEYS] + list(LEGACY_JUNK_FILES):
        try:
            os.remove(os.path.join(folder, fname))
            dropped.append(fname)
        except OSError:
            pass
    return dropped


def migrate_legacy_files(registry_root=None, folder=None):
    """
    首次启动时把老数据搬进新的配置文件。返回 (是否搬了, 说明)。

    每台机器一辈子最多搬一次；数据文件一旦存在就再也不碰老数据。

    registry_root / folder 传 None 就是真实启动（读真实注册表、清程序目录）；
    自检传演练位置，就能把整条迁移链**真的跑一遍**（写进演练数据仓），
    完全不必碰使用者的真实数据 —— 传了参数就说明这是测试在模拟。
    """
    testing = registry_root is not None or folder is not None
    if not testing:
        # 演练目录（自检/端到端测试）永远不迁移：那里的「老数据」是测试造的，
        # 而且迁移会去读真实的注册表 —— 测试绝不能碰使用者的真实数据。
        if os.environ.get("ANCIENT_COUNTDOWN_HOME"):
            return False, "演练目录：不做迁移"
        if os.path.exists(DATA_PATH):
            return False, ""

    bundle = collect_legacy_data(registry_root, folder)
    if not bundle:
        return False, ""

    # 搬家路上顺手把凭据加密。
    #
    # 老数据里授权码是明文的，而新文件本来就该存密文。放在这里加、而不是
    # 等用户下次保存设置，是因为用户可能几个月都不动一次设置 —— 那段时间里
    # 文件里就白白躺着一份明文授权码。seal 过的值再读也没问题
    # （unseal_text 认 dpapi: 前缀；没前缀的当明文原样返回，两种都兼容）。
    sec = bundle.get("notify_secret")
    if isinstance(sec, dict):
        bundle["notify_secret"] = dict(
            (k, seal_text(v) if k in SECRET_FIELDS else v)
            for k, v in sec.items())

    ok, err = _data_file_write(bundle)
    if not ok:
        return False, "老数据搬不过来：%s" % err

    global _data_cache
    _data_cache = bundle

    # 数据已经稳稳落盘，这才动老的 json。顺序不能反 —— 先删后写，
    # 万一写失败就成了真丢数据。
    dropped = drop_legacy_files(folder)
    note = "从老版本搬来 %d 项设置" % len(bundle)
    if dropped:
        note += "，清掉旧文件 %d 个" % len(dropped)
    return True, note


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
    恢复出厂设置的「数据部分」：清空数据文件，再按空仓重新读出三份默认数据。

    为什么要单独拆出一个不带界面的函数：
      · 只删文件是假干净 —— 内存里还抱着旧配置，下一次 tick 记窗口位置、
        或者退出时落盘，都会把旧配置原样写回去，删掉的东西转眼复活，用户点了白点。
        所以删完必须立刻重新加载，让内存也回到初始值。
      · 分开之后，自检脚本可以只测数据这一段（不用开窗口就能断言），
        界面刷新那部分留给 CountdownApp.factory_reset 单独负责。

    ⚠️ 清空之后刻意**留一个空壳文件**，而不是把文件删掉：
    文件只要存在，「从老版本搬一次」那个迁移就不会再跑。要是文件没了，
    下次启动迁移会从注册表把老设置原样搬回来 —— 用户会看到
    「恢复出厂没起作用」，而且完全想不到是这么回事。

    返回 (cfg, secret, notify_state) 三份全新的默认数据。
    notify.signature 由 load_config 按「首次运行」的规则补种本机名，
    和刚装好时一模一样。
    """
    reg_store_drop_all(reg_store_key())
    _data_file_write({})          # 空壳：内容为空，但文件得在（见上面那段）
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
     "hint": "明文写进文件里：别放公共网盘、别发到群里（远程同步永远不带这一项）",
     "drop": (("notify_secret",),)},
    # 为什么"邮件服务商"要单独拆一条、而且默认不带：
    # 授权码是**绑在服务商上的**（它只对某台 SMTP 服务器有效）。而 config.notify
    # 原来是整段同步的 —— 谁改得动那份设置文件（或那个网址上的文件），
    # 谁就能把 host 指到他自己的服务器上，于是用户下一次寄信会把**授权码
    # 连同信件一起送过去**。用户看不见这件事，只会觉得"信没寄出去"。
    # 所以默认不带：想换服务商时再在清单里显式勾上（那时他知道自己在做什么）。
    {"key": "smtp", "label": "邮件服务商（服务器与端口）", "default": False,
     "hint": "默认不带：能改这一项的文件，等于能决定你的授权码发到哪台服务器",
     "drop": (("config", "notify", "host"), ("config", "notify", "port"),
              ("config", "notify", "use_ssl"), ("config", "notify", "provider"))},
    {"key": "shutdown", "label": "定时关机（网址与关机时刻）", "default": True,
     "hint": "各机器的网址或关机时刻不一样的话就别带这一项",
     "drop": (("config", "shutdown"),)},
    {"key": "watch", "label": "窗口盯守设置", "default": True,
     "hint": "盯哪扇窗、隔多久看一次、连续不见多久才寄信",
     "drop": (("config", "watch"),)},
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


def _shape_problems(node, template, path=""):
    """
    拿默认配置当尺子，量一遍这份设置「长得对不对」。返回人说得出话的毛病清单。

    为什么非要有这一层：共用设置是给人手工编辑、拷来拷去的文件，写错一个类型
    （比如把 palette 整段写成 "红色"）在文件里看着毫无异样，导入时也不报错 ——
    直到下次启动，pal["ink"] 取不出来，窗口直接起不来，用户连设置面板都打不开，
    只能去改注册表。所以类型不对就当整份文件不收。

    宁松勿严，是刻意的：
      · 尺子上没有的键（以后新增的、别人加的）一律放行；
      · 只比到容器类型这一层，不查内容（颜色值写错字、端口写 0 都不拦）。
    查太严会把旧版本导出的文件挡在门外，那比放进来更糟。
    """
    out = []
    if not isinstance(template, dict) or not isinstance(node, dict):
        return out
    for key, val in node.items():
        if not isinstance(key, str):
            out.append("%s里有个不是文字的键名" % path)
            continue
        here = "%s%s" % (path, key)
        if key not in template:
            continue                                 # 尺子上没有：放行
        want = template[key]
        if isinstance(want, dict):
            if not isinstance(val, dict):
                out.append("「%s」应该是一段设置，文件里是%s"
                           % (here, type(val).__name__))
            else:
                out += _shape_problems(val, want, here + "·")
            continue
        if isinstance(want, list):
            if not isinstance(val, list):
                out.append("「%s」应该是一个列表，文件里是%s"
                           % (here, type(val).__name__))
            elif want and isinstance(want[0], dict):
                # 列表里每一项都得是「一段设置」：thresholds / notify.rules
                # 都是这种形状，混进一个字符串会让取色那一步直接崩。
                for idx, item in enumerate(val):
                    if not isinstance(item, dict):
                        out.append("「%s」的第 %d 项应该是一段设置"
                                   % (here, idx + 1))
                        break
            continue
        # 标量。真假必须在数字之前判 —— Python 里 True 也是 int，
        # 顺序反了，port 写成 true 会被当成合法数字放进去。
        if isinstance(want, bool):
            if not isinstance(val, bool):
                out.append("「%s」应该填 真/假" % here)
            continue
        if isinstance(want, (int, float)):
            if isinstance(val, bool) or not isinstance(val, (int, float)):
                out.append("「%s」应该填数字" % here)
            continue
        if isinstance(want, str):
            if not isinstance(val, str):
                out.append("「%s」应该填文字" % here)
            continue
        # 默认值是 None 的（比如 window.x「还没定」）不查：它天生可以是 None，
        # 也可以是数字，尺子量不了。
    return out


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

    # 类型筛子。放在 pop 之后：pop 掉的那两项本来就不会被采用，
    # 为它们（可能存在的）类型毛病把整份文件挡回去，只会让人莫名其妙。
    problems = _shape_problems(cfg_in, DEFAULT_CONFIG)
    if problems:
        return False, ("这份文件里的设置类型对不上，没有导入（类型错位会把配置写坏，"
                       "下次连窗口都起不来）：" + "；".join(problems[:4]) + "。"
                       "请对照导出时的原样改回来，或重新导出、重新导入。")

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


# --------------------------------------------------------------------------
# 远程设置 · 从一个网址取回一份设置
#
# 解决这个场景：手上十几台机器，设置要一样。以前靠「导出共用设置 → U 盘拷
# → 挨台导入」；现在把那份文件搁在一个网址上，各台机器自己去取。
#
# 三条规矩，一条都不能松：
#   ① 取回来的东西**只认 config 那一段**。邮箱授权码、认证密码这些凭据
#      一概不认 —— 密码只在本机填。这是这个功能唯一的安全底线：
#      否则「谁控制那个网址，谁就能让你把授权码寄到他的服务器上」。
#   ② 拉不到就什么都不做：保留本机现有设置，只记一行失败原因。
#      断网、服务器挂了、密码填错了，都不该让谁的设置凭空消失。
#   ③ 拉回来的内容必须先过类型筛子才允许落盘 —— 和从 U 盘导入走同一道闸。
# --------------------------------------------------------------------------

REMOTE_TIMEOUT = 20                      # 拉一次最多等这么久
REMOTE_MAX_BYTES = 512 * 1024            # 设置文件不该超过 512 KB

# 界面上那个下拉框里的名字 → 内部代号。
# 分开存是因为「给人看的话」和「写进配置的代号」将来都可能各自变，
# 混在一起写死，改一处就会把老配置里的 auth 值读错。
REMOTE_AUTH_LABELS = (
    ("用户名 + 密码", "basic"),
    ("令牌（一串长码）", "bearer"),
    ("自定义请求头", "header"),
    ("不需要认证", "none"),
)


def remote_auth_label(mode):
    """内部代号 → 界面上显示的名字。认不出来就当 basic。"""
    mode = (mode or "").strip().lower()
    for label, key in REMOTE_AUTH_LABELS:
        if key == mode:
            return label
    return REMOTE_AUTH_LABELS[0][0]


def remote_auth_key(label):
    """界面上显示的名字 → 内部代号。"""
    for text, key in REMOTE_AUTH_LABELS:
        if text == label:
            return key
    return "none"


def remote_item_specs():
    """
    远程同步能勾哪些项：和「导出共用设置」共用同一张表。

    唯一去掉的是「邮箱授权码」那一项 —— 密码永远不从网上取，只在本机填。
    这条不能通融：远端那个文件是放在某个网址上的，
    谁改得动它，谁就相当于指定了「你的授权码往哪个服务器发」。
    """
    return [it for it in SHARED_ITEMS if it["key"] != "secret"]


def default_remote_selection():
    """远程默认同步哪些项。和共用设置的默认一致（目标时刻默认不带）。"""
    return dict((it["key"], bool(it["default"])) for it in remote_item_specs())


def remote_auth_headers(auth, user, secret):
    """
    按认证方式拼出请求头。返回 (headers, 错误说明)。

    纯函数（不联网、不读盘），所以自检能把它整个覆盖掉 —— 认证正是这块
    最容易出错、也最不该出错的地方：拼错了用户只会看到一句「服务器返回 401」，
    根本看不出自己到底少填了什么。
    """
    auth = (auth or "none").strip().lower()
    sec = secret if isinstance(secret, dict) else {}
    if auth == "none":
        return {}, ""
    if auth == "basic":
        import base64
        user = (user or "").strip()
        if not user:
            return None, "选了「用户名 + 密码」，但用户名是空的"
        raw = ("%s:%s" % (user, sec.get("remote_password") or "")).encode("utf-8")
        return {"Authorization": "Basic " + base64.b64encode(raw).decode("ascii")}, ""
    if auth == "bearer":
        token = (sec.get("remote_token") or "").strip()
        if not token:
            return None, "选了「令牌」，但令牌是空的"
        return {"Authorization": "Bearer " + token}, ""
    if auth == "header":
        name = (sec.get("remote_header_name") or "").strip()
        if not name:
            return None, "选了「自定义请求头」，但头名称是空的"
        return {name: sec.get("remote_header_value") or ""}, ""
    return None, "认证方式「%s」不认识" % auth


def fetch_remote_config(url, auth="none", user="", secret=None,
                        timeout=REMOTE_TIMEOUT):
    """
    去远处取一份设置。返回 (包, None) 或 (None, 错误说明)。

    只认 http / https；网址少了协议头就补 http:// —— 用户十有八九只写域名。
    """
    url = (url or "").strip()
    if not url:
        return None, "还没填网址"
    if not re.match(r"^https?://", url, re.I):
        url = "http://" + url

    headers, err = remote_auth_headers(auth, user, secret)
    if headers is None:
        return None, err

    data, err = _http_get(url, timeout=timeout, max_bytes=REMOTE_MAX_BYTES,
                          headers=headers)
    if data is None:
        return None, err
    try:
        bundle = json.loads(data.decode("utf-8-sig", "replace"))
    except ValueError:
        return None, ("取回来的内容不是一个设置文件（不是合法的 JSON）。"
                      "看看网址指向的是不是设置文件本身。")
    if not isinstance(bundle, dict):
        return None, "取回来的内容不是一个设置文件（最外层应该是一对花括号）"
    return bundle, None


def apply_remote_config(bundle, items=None):
    """
    把远端那份设置应用进来。返回 (是否采用, 说明)。

    只认 config 段 —— notify_secret（邮箱授权码、远程凭据）永远不动。
    勾选剔除、类型筛子、与现有配置合并，全部走和「从 U 盘导入」同一套代码，
    保证两条路的行为分毫不差。
    """
    if not isinstance(bundle, dict):
        return False, "取回来的不是一个设置对象"
    cfg_in = bundle.get("config")
    if not isinstance(cfg_in, dict):
        return False, "取回来的东西里没有 config 这一段"

    cfg_in = json.loads(json.dumps(cfg_in))
    cfg_in.pop("autostart", None)
    nd = cfg_in.get("notify")
    if isinstance(nd, dict):
        nd.pop("signature", None)
    # 远端绝不能改写本机的「远程设置」本身（网址、认证方式、凭据）——
    # 那等于让远端决定「下次去哪儿取配置」。
    cfg_in.pop("remote", None)

    problems = _shape_problems(cfg_in, DEFAULT_CONFIG)
    if problems:
        return False, ("远端这份设置的类型对不上，没有采用（类型错位会把配置"
                       "写坏，下次连窗口都起不来）：" + "；".join(problems[:4]))

    if items is not None:
        picked = set(it["key"] for it in remote_item_specs() if items.get(it["key"]))
        # 复用共用设置那张表里的剔除路径（形如 ("config", "notify")）——
        # 装进一个临时包再剔，走的就是导出那条路上的同一段代码。
        wrapper = {"config": cfg_in}
        for spec in remote_item_specs():
            if spec["key"] in picked:
                continue
            for path in spec["drop"]:
                _drop_shared_path(wrapper, path)

    cur = reg_store_read("config", {})
    if not isinstance(cur, dict):
        cur = {}
    merged = deep_merge(cur, cfg_in)
    ok, err = reg_store_write("config", merged)
    if not ok:
        return False, "设置写不进去：%s" % err
    return True, ""


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


# 凭据段里这些字段落盘一律加密、读出一律解密。
# 同一个段里放了两处密码：邮箱授权码，和远程配置的认证凭据 ——
# 它们的共同点是「绝对不能让别人拿到」，所以走同一道加解密。
SECRET_FIELDS = ("smtp_password", "remote_password", "remote_token",
                 "remote_header_name", "remote_header_value")


def load_notify_secret():
    sec = reg_store_read("notify_secret", {})
    if not isinstance(sec, dict):
        sec = {}
    for name in SECRET_FIELDS:
        sec.setdefault(name, "")
        # 磁盘上存的是密文，内存里一律换成明文 —— 发信进程要拿授权码去登录。
        # 解不开（配置从别的机器拷来）就是空串，界面会提示重填，不算错误。
        sec[name] = unseal_text(sec.get(name))
    return sec


def save_notify_secret(sec):
    """凭据落盘前加密。加密失败会自动退回明文，绝不因此让密码用不成。"""
    out = dict(sec or {})
    for name in SECRET_FIELDS:
        out[name] = seal_text(out.get(name))
    return reg_store_write("notify_secret", out)


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

# --------------------------------------------------------------------------
# 定时关机 · 从自己的网站取日期数字
# --------------------------------------------------------------------------
#
# 这一节只做三件事：把网址上的内容读成一个时刻、把时刻写回配置、到点执行关机。
# 联网与开机关机的动作都放在独立进程 / 后台线程里（见 app.fetch_site_now），
# 主进程只做「时间到了没有」这种减法 —— 和传书那一套是同一个思路。

def _walk_scalars(node, depth=0):
    """把一个 JSON 结构里所有标量值摊平（含嵌套的字典与数组）。"""
    if depth > 6:
        return
    if isinstance(node, dict):
        for value in node.values():
            for item in _walk_scalars(value, depth + 1):
                yield item
    elif isinstance(node, (list, tuple)):
        for value in node:
            for item in _walk_scalars(value, depth + 1):
                yield item
    elif isinstance(node, (str, int, float)):
        yield node


def _compact_digits_dt(text):
    """
    把光秃秃的一串数字读成时刻：20261001 / 202610011130 / 20261001113000。

    「一串日期数字」最省事的形式就是把年月日时分直接连起来，中间一个标点都不给。
    这种写法 parse_target 读不通（它把整串当成一个数字，只好拒绝），所以单独认一下。

    开头必须是 19 / 20：这样 1759041000 这类时间戳不会被猜成 1975 年 9 月 ——
    猜错的日子比读不通更坏，读不通至少还能报个「没找到日期」。
    """
    s = str(text or "").strip()
    if not s.isdigit() or len(s) not in (8, 10, 12, 14):
        return None
    if s[:2] not in ("19", "20"):
        return None
    try:
        return datetime.datetime(
            int(s[0:4]), int(s[4:6]), int(s[6:8]),
            int(s[8:10]) if len(s) >= 10 else 0,
            int(s[10:12]) if len(s) >= 12 else 0,
            int(s[12:14]) if len(s) >= 14 else 0)
    except ValueError:
        return None


def _epoch_dt(text):
    """10 位（秒）/ 13 位（毫秒）时间戳。认不出返回 None。"""
    s = str(text or "").strip()
    if not s.isdigit() or len(s) not in (10, 13):
        return None
    try:
        value = int(s)
        if len(s) == 13:
            value //= 1000
        if not 946684800 <= value <= 4102444800:      # 2000-01-01 ~ 2100-01-01
            return None
        return datetime.datetime.fromtimestamp(value)
    except (ValueError, OSError, OverflowError):
        return None


def extract_target(raw, now=None):
    """
    从网站返回的内容里挖出一个能认的时刻。返回 (datetime | None, 认到的原文)。

    为什么要这么宽容：那个网站是用户自己写的，返回什么谁也说不准 ——
    可能是一句纯日期数字，可能是 JSON 里的某个字段，也可能是一段带标签的网页。
    与其让他去对齐一个约定，不如这边把常见形式全认下来：

        ① 整段就是一个日期数字（"10.1.11.30"、"2026-10-01 11:30"）
        ② 年月日连成一串（"202610011130"）
        ③ 时间戳（10 位秒 / 13 位毫秒）
        ④ JSON：把所有字段值摊平，一个个试
        ⑤ 带标签 / 带引号的文本：抠出像日期的小段再试

    认不出来就明说认不出来，绝不猜 —— 猜出一个看着合理的错时间，
    用户要到倒计时归零、机器真关了才发现。
    """
    if isinstance(raw, bytes):
        raw = raw.decode("utf-8", "ignore")
    text = str(raw or "").strip()
    if not text:
        return None, ""

    def attempt(cand):
        cand = str(cand).strip()
        if not cand:
            return None
        got, _err = parse_target(cand, now=now)
        if got is not None:
            return got
        return _compact_digits_dt(cand) or _epoch_dt(cand)

    cands = [text]
    try:
        data = json.loads(text)
    except ValueError:
        data = None
    if data is not None:
        cands.extend(str(v) for v in _walk_scalars(data))
    # 带标签的文本：去掉标签后，抠出「数字开头 + 数字/日期符号」的小段。
    # 这一段不含空格 —— 含空格的话，整行说明文字都会被当成一个候选。
    flat = re.sub(r"<[^>]*>", " ", text)
    cands.extend(re.findall(r"\d[\d.\-/年月日时分:：]{0,24}", flat))

    seen = set()
    for cand in cands:
        key = cand.strip()
        if not key or key in seen:
            continue
        seen.add(key)
        got = attempt(key)
        if got is not None:
            return got, key[:60]
    return None, ""


def canonical_target(dt):
    """
    把时刻写成「存进配置、下次还能读回同一个时刻」的写法。

    必须带四位年份：不带年份时解析器会挑「下一个还没到的」那一年，
    跨年目标会被它悄悄挪到明年 —— 存进去和读出来的就不是同一个时刻了。
    """
    return dt.strftime("%Y.%m.%d.%H.%M")


def target_text_of(dt):
    """
    时刻 → 配置文本。在 canonical_target 的基础上多管一件事：
    带秒的目标把秒也写上，读回来分毫不差（整分的照旧省掉秒，
    免得配置里挂一串无意义的「.0」尾巴）。
    """
    if dt.second:
        return dt.strftime("%Y.%m.%d.%H.%M.%S")
    return canonical_target(dt)


def extend_target_text(text, days=30, now=None):
    """
    「倒计时 + N 天」的一口价算法（右键菜单与设置面板共用这一个按钮）。

    规则是用户点名要的：
      · 没过期 —— 在原时刻上加 N 天；
      · 已过期、没设过、或原文读不通 —— 从现在起算 N 天。
        （过期了还按原时刻加，加出来的仍是过去，等于白加。）

    返回**带年份**的文本。为什么非要带年份：不带年份的目标一旦过期，
    解析器会把它顺到「明年的同一天」（那是给「设置时还没到」准备的规则），
    于是重启一次程序，界面就从「時辰已到」变成「还剩三百多天」——
    这正是这个按钮要一并堵住的洞。运行中归零由 _latch_zero 钉住，
    手动改时刻走这里，两条路都通向「带年份」。

    纯函数：不碰配置、不碰界面，自检直接整个覆盖。
    """
    now = now or datetime.datetime.now()
    try:
        days = max(1, int(days))
    except (TypeError, ValueError):
        days = 30
    got, _err = parse_target(text, now)
    base = got if (got is not None and got > now) else now
    return target_text_of(base + datetime.timedelta(days=days))


def fetch_site_target(url, timeout=SITE_FETCH_TIMEOUT, now=None):
    """
    去用户自己的网站取那一串日期数字。

    返回 (datetime, 认到的原文, None) 或 (None, 收到的原文, 错误说明)。

    只认 http / https；网址少了协议头就补 http:// —— 用户十有八九只写域名。
    """
    url = (url or "").strip()
    if not url:
        return None, "", "还没填网址"
    if not re.match(r"^https?://", url, re.I):
        url = "http://" + url
    data, err = _http_get(url, timeout=timeout, max_bytes=SITE_MAX_BYTES)
    if data is None:
        return None, "", err
    text = data.decode("utf-8", "ignore")
    got, used = extract_target(text, now=now)
    if got is None:
        brief = re.sub(r"\s+", " ", text).strip()[:120]
        return None, text, "返回内容里没找到能认的日期数字（收到的是：%s）" % (brief or "空内容")
    return got, used, None


def shutdown_key_of(source, dt):
    """
    一个关机时刻的身份证。格式 `来源|时刻`。

    拿它认「这件事办过没有」—— 时刻换一个字符串就换一个，所以
    「改过倒计时目标」＝ 一件新事，旧记录不会把它挡住。
    带来源前缀是因为两个来源可能给出**一模一样**的时刻，
    那种情况下它们是两件事，不该互相顶掉。
    """
    return "%s|%s" % (source, dt.strftime("%Y-%m-%dT%H:%M:%S"))


def run_shutdown(grace_sec=0):
    """
    调 Windows 自带的关机命令。返回 (是否已发出, 失败说明)。

    默认 /t 0 —— **立刻关**。反悔的机会已经在前面那道确认窗里给过了
    （见 ShutdownAlertWindow）：那儿不点才轮到这一步，再留一段缓冲
    等于把同一个问题问两遍。grace_sec 留着是给别处（比如将来做静默关机）用。

    不动用 at / 计划任务：那个改起来麻烦，而且本程序自己就是那个钟。
    """
    import subprocess
    try:
        sec = max(0, min(int(grace_sec), SHUTDOWN_GRACE_MAX))
    except (TypeError, ValueError):
        sec = SHUTDOWN_GRACE_DEFAULT
    # 注释要短：shutdown /c 的上限是 512 字符，超了整条命令直接报错不执行
    tip = ("古风倒计时：时刻已到，正在关机。" if sec <= 0
           else "古风倒计时：时刻已到，%d 秒后关机。要取消就打开本程序点「取消定时关机」。"
                % sec)
    flags = 0x08000000 if os.name == "nt" else 0        # CREATE_NO_WINDOW
    try:
        subprocess.Popen(
            ["shutdown", "/s", "/t", str(sec), "/c", tip],
            creationflags=flags, close_fds=True,
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL)
    except Exception as exc:                            # noqa: BLE001
        return False, str(exc)
    return True, ""


def cancel_shutdown():
    """
    取消已经排上的关机（shutdown /a）。返回 (是否已发出, 失败说明)。

    本来就没有排过关机时，这条命令会报「1116 找不到进行中的关机」然后退出 ——
    那是正常的，不当失败看。
    """
    import subprocess
    flags = 0x08000000 if os.name == "nt" else 0
    try:
        subprocess.Popen(
            ["shutdown", "/a"],
            creationflags=flags, close_fds=True,
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL)
    except Exception as exc:                            # noqa: BLE001
        return False, str(exc)
    return True, ""


def load_shutdown_state():
    """
    这次关机推进到哪一步了。

    几个字段各管一件事，别混：
      target_key   正在处理（或已经处理过）的那个时刻，形如 `target|2026-10-05T00:00:00`。
                   它一变就代表「这是另一件事」—— 换过倒计时目标就会变，
                   旧记录不会把新目标挡住（老版本存的是不带来源前缀的纯时刻，
                   和新格式对不上，效果是「重新认一次」，安全）。
      phase        ""  空闲
                   asking  确认窗开着，等用户表态
                   retrying 命令已经发过一次，一分钟后再看机器关没关
      tries        这次关机一共发过几次命令
      next_try     下一次允许动手的时间戳（重试档用）
    """
    st = reg_store_read(SHUTDOWN_STATE_KEY, {})
    if not isinstance(st, dict):
        st = {}
    for key, blank in (("target_key", ""), ("source", ""), ("phase", ""),
                       ("fired_at", ""), ("cancelled_at", ""),
                       ("missed_at", ""), ("note", "")):
        st.setdefault(key, blank)
    for key in ("tries", "next_try"):
        st.setdefault(key, 0)
    return st


def save_shutdown_state(st):
    return reg_store_write(SHUTDOWN_STATE_KEY, st)


# --------------------------------------------------------------------------
# 窗口盯守 · 看某扇窗还在不在
# --------------------------------------------------------------------------
#
# 「在不在」这件事只能问系统。这里用 EnumWindows 把所有可见的顶层窗口标题列一遍，
# 再用关键字去比 —— 不比对进程、不比对类名，因为那两样用户既看不见也说不清，
# 而窗口标题正是他在下拉框里点得中的东西。
#
# 标题会变（游戏标题里常带角色名、等级、在线人数），所以存的是**关键字**：
# 点一下下拉框选到「某某游戏」，存进去的就是整条标题；觉得太长了可以自己删短，
# 只要那一段还在标题里就认得出来。

# 本程序自己的窗口不该出现在候选里 —— 它一直在，选错了等于永远「窗口都在」
OWN_WINDOW_HINTS = ("古风倒计时", "設 置", "传 书 记 录", "盯 守", "导出共用设置")
# 系统里几扇始终存在的窗口，列出来只会碍事
JUNK_WINDOW_TITLES = ("Program Manager", "Default IME", "MSCTFIME UI",
                      "Windows 输入体验", "Windows Input Experience",
                      "Hidden Window", "Task Host Window")


def _squeeze(text):
    """压掉所有空白再比 —— 「游戏 名称」和「游戏名称」该算同一个。"""
    return re.sub(r"\s+", "", str(text or "")).lower()


def _is_own_window(title):
    t = str(title or "").strip()
    if not t:
        return True
    if t in JUNK_WINDOW_TITLES:
        return True
    for hint in OWN_WINDOW_HINTS:
        if hint in t:
            return True
    return False


def list_windows():
    """
    当前所有可见的顶层窗口标题（去重、去掉本程序与系统外壳的）。

    取不到就返回空列表 —— 界面会显示「没找到窗口」，而不是崩掉。
    """
    if os.name != "nt":
        return []
    try:
        import ctypes
        from ctypes import wintypes
        user32 = ctypes.windll.user32
        # 这几行的原型必须写死：64 位下句柄是 8 字节，默认的 c_int 会被截断，
        # 截断之后的句柄传给 GetWindowTextW 就是另一个窗口（或直接失败）。
        user32.GetWindowTextLengthW.argtypes = [wintypes.HWND]
        user32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
        user32.IsWindowVisible.argtypes = [wintypes.HWND]
        user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND,
                                                    ctypes.POINTER(wintypes.DWORD)]
    except Exception:                                   # noqa: BLE001
        return []

    own_pid = os.getpid()
    found = []

    def collect(hwnd, _lparam):
        try:
            if not user32.IsWindowVisible(hwnd):
                return True
            # 按进程号把「本程序自己的窗口」滤掉。
            #
            # 为什么不按标题滤：设置面板 / 问话窗都是无边框的 Toplevel，
            # 在系统眼里它们的标题就是 Tk 的默认值「tk」—— 拿标题去滤，
            # 要么滤不干净，要么把用户真正想挑的那扇窗一起误伤。
            # 进程号是精确的，而且一眼看得出在滤什么。
            pid = wintypes.DWORD()
            user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value == own_pid:
                return True
            length = user32.GetWindowTextLengthW(hwnd)
            if length <= 0:
                return True
            buf = ctypes.create_unicode_buffer(length + 1)
            user32.GetWindowTextW(hwnd, buf, length + 1)
            title = (buf.value or "").strip()
        except Exception:                               # noqa: BLE001
            return True
        if title and title not in found and not _is_own_window(title):
            found.append(title)
        return True

    try:
        proc = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
        user32.EnumWindows(proc(collect), 0)
    except Exception:                                   # noqa: BLE001
        return []
    return found[:WINDOW_LIST_MAX]


def window_present(keyword, titles=None):
    """这扇窗在不在。keyword 为空一律算「不在」——否则空关键字会匹配上一切。"""
    kw = _squeeze(keyword)
    if not kw:
        return False
    pool = list_windows() if titles is None else titles
    for title in pool:
        if kw in _squeeze(title):
            return True
    return False


def tick_count():
    """开机以来的毫秒数（GetTickCount64，随开机归零）。取不到就返回 0。"""
    if os.name != "nt":
        return 0
    try:
        import ctypes
        return int(ctypes.windll.kernel32.GetTickCount64())
    except Exception:                                   # noqa: BLE001
        return 0


def boot_at():
    """
    本次开机的墙上时钟时刻（epoch 秒）。

    开机毫秒数随开机归零，拿它和 time.time() 一减就是「这次开机是几点」。
    盯守靠它判断「机器重启过没有」—— 见 _disarm_watch_after_reboot。
    时钟被调过会让它有偏差，调用处按容差（WATCH_BOOT_DRIFT_SEC）处理。
    """
    t = tick_count()
    if not t:
        return 0.0
    return time.time() - t / 1000.0


def load_watch_state():
    st = reg_store_read(WATCH_STATE_KEY, {})
    if not isinstance(st, dict):
        st = {}
    st.setdefault("phase", "")          # "" / waiting / watching / pending / off
    st.setdefault("keyword", "")
    st.setdefault("seen_at", "")
    st.setdefault("note", "")
    st.setdefault("rounds", 0)
    st.setdefault("last_probe", 0.0)
    st.setdefault("seen_boot", 0.0)     # 上次看见那扇窗时的开机时刻（判断机器重启过没有）
    st.setdefault("pend_probe", 0.0)    # 问话期间上一次核实窗口在不在的时刻
    if not isinstance(st.get("pending"), dict):
        st["pending"] = {}
    return st


def save_watch_state(st):
    return reg_store_write(WATCH_STATE_KEY, st)


def load_alert_state():
    st = reg_store_read(ALERT_STATE_KEY, {"items": []})
    if not isinstance(st, dict):
        st = {"items": []}
    if not isinstance(st.get("items"), list):
        st["items"] = []
    return st


def save_alert_state(st):
    return reg_store_write(ALERT_STATE_KEY, st)


class CountdownApp:

    def __init__(self):
        self.cfg = load_config()
        self.target, self.parse_err = parse_target(self.cfg.get("target"))

        self.remaining = None
        self.zero_mode = False
        self._zero_latched = False     # 这一轮归零有没有钉过时刻（见 _latch_zero）
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

        # 定时关机与窗口盯守：一样只持有内存引用，注册表那三个值读起来是毫秒级，
        # 对启动速度没有可感影响。
        self.site_date = reg_store_read(SITE_STATE_KEY, {})
        if not isinstance(self.site_date, dict):
            self.site_date = {}
        self.shutdown_state = load_shutdown_state()
        self.watch_state = load_watch_state()
        self.alert_state = load_alert_state()
        self._settle_shutdown_after_restart()
        self._site_fetching = False     # 取日期正在进行中，防重复点
        self._alert_win = None          # 「窗口不见了」那扇确认窗（真出事时）
        self._drill_win = None          # 「试一遍」演练用的那扇窗（另占一个槽）
        self._disarm_watch_after_reboot()   # 机器重启过 → 盯守推回「等出现」
        self._watch_note = ""
        # 下一次允许自动取日期的时刻。启动后先静置二十秒：一是把开机那几秒
        # 留给窗口本身（别让它跟启动抢网络），二是刚开机时网络栈往往还没起来，
        # 那会儿去取必然失败，白记一笔「取不到」。
        self._site_next_at = time.time() + SITE_FETCH_START_DELAY
        # 远程设置：同样先静置二十秒再拉第一次（理由和取关机时刻一样）。
        # 静置的是「自动拉」；用户在面板上点「现在就拉」不受这个限制。
        self._remote_fetching = False
        self._remote_next_at = time.time() + SITE_FETCH_START_DELAY
        # 远程关机时刻 —— 只由「网址取回的数字」或「设置文件里写死的 at」
        # 决定，**自己单独一份**。
        # 单独存的原因：它和 self.target 是两件事，用户设的倒计时不该被
        # 「去网站取了一次数」悄悄换掉（v1.6 就是这么错的，别退回那个做法）。
        # 从数据仓里恢复，所以重启程序之后还认得已经排上的关机时刻。
        # 到点关机时它和 self.target 一起参选，谁先到谁关。
        self.shutdown_at = self._restore_shutdown_at()
        # 有哪些关机时刻是**亲眼看着它还没到**的（记身份证，见 shutdown_key_of）。
        # 关机只认这一种情况：程序不在运行的那段时间里时刻悄悄过去了
        # （关机三天后开机就是这种），一开机就执行关机是很吓人的事。
        # 两个来源各记各的 —— 远程那个刚换过，不代表本地那个也要重新见过。
        self._armed_keys = set()
        self._shutdown_win = None       # 「马上要关机」那扇确认窗

        # 字号缓存：字体切换在 Tk 中约 8ms，必须避免每秒重新试错
        self._digits_key = None
        self._digits_size = 100
        self._zero_key = None
        self._zero_size = 100

        # 常驻图元：数字那八件与右上角按钮那三件各只创建一次，之后只改
        # 真正变化的那几项。这一层专门用来压掉「每帧 delete + 重建」的
        # Tcl 往返次数 —— Tk 的每一次 create/coords/itemconfigure 都是
        # 一次跨语言调用，旧实现每帧固定 25 次（1 删 + 8 建 + 16 度量）。
        # 实测：数字刷新 1.86ms -> 0.32ms/帧，按钮重绘 2.7ms -> 0.008ms。
        # 注意 layout() 里会 canvas.delete("all")，届时这些 id 全部失效，
        # 必须在那边一并清空（见 _forget_canvas_items）。
        self._dyn_ids = None
        self._dyn_text = [None] * 8
        self._dyn_xy = [None] * 8
        self._dyn_fg = None
        self._measure_cache = {}
        self._ctl_ids = None
        self._ctl_xy = [None] * 3
        self._ctl_fill = [None] * 3
        self._ctl_dot = None
        self._gear_size = None          # 右上角三颗字的当前字号（见 _draw_controls）
        self._cursor = "fleur"

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
        # 放第一项：这个按钮最重要的用场是「倒计时归零了」那一刻 ——
        # 界面上正好闪着「時辰已到」，用户此时最不需要的是去翻菜单找入口。
        m.add_command(label="　　倒计时 +30 天",
                      command=lambda: self.extend_target_days(30))
        m.add_command(label="　　设置…", command=self.open_settings)
        # 关机正在推进时才多出这一项：那一刻用户多半正忙着找地方反悔，
        # 藏在设置面板里等于不给他退路。确认窗开着的、以及命令已经发出去
        # 正等着重试的，两种都得能停 —— 少一种他就只能干看着机器被关。
        if self.shutdown_armed():
            m.add_command(label="　　取消定时关机", command=self.shutdown_cancel_now)
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
        self._forget_canvas_items()
        self._draw_paper(W, H, bg)
        self._draw_frame(W, H)
        self._draw_controls(W, H)
        self._draw_seal(W, H)
        self._draw_head(W, H)
        self.redraw_dynamic()

    def _forget_canvas_items(self):
        """
        画布被整幅清空后，把常驻图元的 id 全部作废。

        layout() 会 canvas.delete("all")，那些 id 指向的图元已经不存在；
        不重置的话，下一次 _draw_digits 会对着已销毁的图元调 coords，
        直接抛 TclError，而且是在每秒的 tick 里抛。
        """
        self._dyn_ids = None
        self._dyn_text = [None] * 8
        self._dyn_xy = [None] * 8
        self._dyn_fg = None
        self._ctl_ids = None
        self._ctl_xy = [None] * 3
        self._ctl_fill = [None] * 3
        self._ctl_dot = None

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

        三个字只创建一次，之后鼠标进出只改颜色。旧实现每次 hover 变化都
        delete + 重建，实测 2.7ms —— 鼠标在按钮附近晃动时是看得见的开销，
        现在同一条路径降到 0.008ms。整组图元统一挂 "gear" 标签，
        需要重建时先删干净，避免一层层叠上去。
        """
        pal = self.cfg["palette"]
        m = max(7, int(min(W, H) * 0.030))
        want = max(10, min(15, int(H * 0.058)))
        # 当前字号记在自己身上，不去问字体对象（f_gear.cget("size")）。
        # 问一次就是一次跨语言调用，而这条路径的整个意义就是「别多花冤枉钱」；
        # 顺带也让测试里那个替身字体（只有一个 configure）能跑通 ——
        # 测试要拦的本来就是「字号变了没重建图元」，不是「拿字号的方式」。
        if self._gear_size != want:
            self.f_gear.configure(size=want)
            self._gear_size = want
            self._ctl_ids = None          # 字号变了，图元要按新字号重建
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
        faint = self._ink_tone("faint")

        ids = self._ctl_ids
        if ids is None or len(ids) != 3:
            self.canvas.delete("gear")
            ids = [self.canvas.create_text(0, 0, text=glyph,
                                           font=self.f_gear, tags="gear",
                                           fill=faint)
                   for _name, glyph in (("gear", "設"), ("min", "—"),
                                        ("close", "✕"))]
            self._ctl_ids = ids
            self._ctl_xy = [None] * 3
            self._ctl_fill = [None] * 3
            self._ctl_dot = None

        for i, name in enumerate(("gear", "min", "close")):
            x, y = self._ctl_pos[name]
            if self._ctl_xy[i] != (x, y):
                self.canvas.coords(ids[i], x, y)
                self._ctl_xy[i] = (x, y)
            col = pal["seal"] if self._ctl_hover == name else faint
            if self._ctl_fill[i] != col:
                self.canvas.itemconfigure(ids[i], fill=col)
                self._ctl_fill[i] = col

        self._draw_version_dot(W, H, pal)

    def _draw_version_dot(self, W, H, pal):
        """
        有新版本时在「設」左上角点一颗朱砂小点；不写字、不弹窗。

        想升级的人自然会去点「設」，不想升级就一直是一颗点，不打扰。
        这颗点同样只建一次，位置变了才动它。
        """
        dot = self._ctl_dot
        if not self.new_version:
            if dot is not None:
                self.canvas.delete(dot)
                self._ctl_dot = None
            return
        gx, gy = self._ctl_pos["gear"]
        r = max(2.5, min(W, H) * 0.011)
        cx, cy2 = gx + r * 3.0, gy - r * 3.0
        box = (cx - r, cy2 - r, cx + r, cy2 + r)
        if dot is None:
            self._ctl_dot = self.canvas.create_oval(
                box[0], box[1], box[2], box[3],
                fill=pal["seal"], outline="", tags="gear")
        else:
            self.canvas.coords(dot, box[0], box[1], box[2], box[3])

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
        """
        刷新「会变的那部分」。

        数字走常驻图元 + 按变化更新（见 _draw_digits），不再整批重建；
        归零与错误两种状态是整段换文字，维持重建，但先把常驻 id 作废，
        免得下一次回到数字态时拿着早已删掉的 id 去改。
        """
        if self.target is None:
            self.canvas.delete("dyn")
            self._dyn_ids = None
            self._draw_error()
        elif self.zero_mode:
            self.canvas.delete("dyn")
            self._dyn_ids = None
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

    def _measure_cached(self, is_num, text, size):
        """
        带缓存的字体度量。

        数字与单位在绝大多数秒里都没变，宽度自然也没变。原实现每帧要调
        16 次 measure（每次都是一次 Tcl 往返），这里按
        「数字还是单位 + 文本 + 字号」缓存，命中后零 Tcl 调用。
        字号一旦变化，调用方会清空整个缓存，所以不存在取到旧字号的宽度。
        """
        key = (is_num, text, size)
        got = self._measure_cache.get(key)
        if got is None:
            font = self.f_num if is_num else self.f_unit
            got = font.measure(text)
            self._measure_cache[key] = got
        return got

    def _draw_digits(self):
        """
        每秒刷新那四组数字。

        与旧实现的关键区别：**图元只建一次，之后只在真的变化时才碰 Tcl**。
        旧实现每帧固定 25 次 Tcl 往返（1 次 delete + 8 次 create_text +
        16 次 measure）；新实现通常只有「秒」那一项真的在变，即 1~2 次。
        实测（真实跳秒、180 帧、A-B-A 三轮）：1.86ms -> 0.32ms/帧，
        图元快照与旧实现逐字段一致（外观不变）。

        ⚠️ 不要"顺手"改成每帧无条件 coords + itemconfigure：那样每项要
        2 次 Tcl 调用，比 create_text 的 1 次还多，实测反而涨到 2.83ms。
        这个函数的性能全看「能跳过多少次 Tcl 往返」。
        """
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
            self._measure_cache = {}      # 字号变了，旧的度量全部作废
            self._dyn_ids = None          # 字号变了，图元要按新字号重建
        size = self._digits_size
        self._ensure_num_size(size)

        gap, grp = self._num_spacing(size)
        fg = (self.theme or {}).get("fg") or pal["default_fg"]
        fg_unit = mix(fg, self.bg_color, 0.28)
        cy = (top + bottom) / 2.0

        # 宽度全部走缓存，同时把这一帧的总宽算出来（它决定整体居中位置）
        widths = []
        total = 0
        for num, unit, _is_sec in pairs:
            nw = self._measure_cached(True, num, size)
            uw = self._measure_cached(False, unit, size)
            widths.append((nw, uw))
            total += nw + gap + uw
        total += grp * (len(pairs) - 1)

        ids = self._dyn_ids
        if ids is None or len(ids) != 8:
            c.delete("dyn")
            ids = [c.create_text(0, 0, text="", font=self.f_num, fill=fg,
                                 tags="dyn") for _ in range(8)]
            # 单位那四个是左对齐的（与原实现一致），建的时候就要定好
            for j in range(0, 8, 2):
                c.itemconfigure(ids[j + 1], font=self.f_unit, anchor="w")
            self._dyn_ids = ids
            self._dyn_text = [None] * 8
            self._dyn_xy = [None] * 8
            self._dyn_fg = None

        recolour = self._dyn_fg != fg
        self._dyn_fg = fg

        x = left + max(0.0, (avail_w - total) / 2.0)
        for i, (num, unit, _is_sec) in enumerate(pairs):
            nw, uw = widths[i]
            i1, i2 = ids[i * 2], ids[i * 2 + 1]

            if self._dyn_text[i * 2] != num:
                c.itemconfigure(i1, text=num)
                self._dyn_text[i * 2] = num
            if recolour:
                c.itemconfigure(i1, fill=fg)
            xy1 = (x + nw / 2.0, cy)
            if self._dyn_xy[i * 2] != xy1:
                c.coords(i1, xy1[0], xy1[1])
                self._dyn_xy[i * 2] = xy1

            if self._dyn_text[i * 2 + 1] != unit:
                c.itemconfigure(i2, text=unit)
                self._dyn_text[i * 2 + 1] = unit
            if recolour:
                c.itemconfigure(i2, fill=fg_unit)
            xy2 = (x + nw + gap, cy + size * 0.29)
            if self._dyn_xy[i * 2 + 1] != xy2:
                c.coords(i2, xy2[0], xy2[1])
                self._dyn_xy[i * 2 + 1] = xy2

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

        # 顺带看一眼有没有第二个实例在喊「现身」（一次注册表读，开销可忽略）。
        # 这里也单独兜住：抛出去就是整条 tick 链断掉，代价是「倒计时不动 +
        # 到点不关机」—— 为了一个顺带动作赔上主功能，完全不值。
        if reg_store_read("wake", None) is not None:
            try:
                self._consume_wake()
            except Exception as exc:              # noqa: BLE001
                log_problem("唤醒", type(exc), exc, exc.__traceback__)

        # 传书巡检。每 30 秒才真跑一次 —— 中间那些秒只是一次减法比较，
        # 在纳秒量级，实测不出与改造前的差别。
        # 首次 tick 必然触发，相当于开机时补做一次「错过的提醒」。
        # 同样单独兜住：传书要碰 SMTP 与网络，是这里最可能出岔子的一段。
        clock = now.timestamp()
        if clock - self._last_notify_check >= NOTIFY_CHECK_SEC:
            self._last_notify_check = clock
            try:
                self.notify_tick(now)
            except Exception as exc:              # noqa: BLE001
                log_problem("传书", type(exc), exc, exc.__traceback__)

        # 定时关机与窗口盯守。
        #
        # 两者每次都是一次时间比较（看时刻到没到、看距上次巡检够不够久），
        # 真正动手的时刻很少：关机一辈子一次，窗口巡检默认半小时一次。
        #
        # 各自单独兜异常，而且是**在这里**兜：它们出岔子可以，把 tick 这条链
        # 带断不行 —— 链一断，倒计时就不走了，关机也不会再发生，
        # 而「到点关机」正是这套功能存在的全部理由。
        for label, probe in (("定时关机", self.shutdown_tick),
                             ("取关机时间", self.site_fetch_tick),
                             ("窗口盯守", self.watch_tick),
                             ("远程设置", self.remote_fetch_tick)):
            try:
                probe(now)
            except Exception as exc:              # noqa: BLE001
                log_problem(label, type(exc), exc, exc.__traceback__)

        # 自动检查更新：启动后先静置 60 秒，之后每 6 小时醒一次。
        # 醒来也不一定真查 —— 要不要发网络请求，得看「距上次查通满没满 7 天」，
        # 而那只是一次数据读。绝大多数巡检到这里就是一次时间戳比较。
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
            # 归零的第一帧把目标时刻钉成带年份的写法（见 _latch_zero）——
            # 不钉的话，重启一次就被解析器顺到明年，倒计时变成三百多天。
            if self.zero_mode and not self._zero_latched:
                self._latch_zero()
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
            self._set_cursor("hand2")
            return

        mode = self.hit_test(event.x, event.y)
        cursor = {"nw": "size_nw_se", "se": "size_nw_se",
                  "ne": "size_ne_sw", "sw": "size_ne_sw",
                  "n": "size_ns", "s": "size_ns",
                  "w": "size_we", "e": "size_we"}.get(mode, "fleur")
        self._set_cursor(cursor)

    def _set_cursor(self, cursor):
        """
        只在光标形状真的变了才写 canvas。

        鼠标移动是高频事件（普通鼠标也能到每秒上百次），而
        canvas.configure 每次都是一次 Tcl 往返；形状没变就整个跳过，
        省掉绝大多数往返。

        ⚠️ canvas 的光标只许经本函数写。self._cursor 是它的缓存，别处
        直接 canvas.configure(cursor=...) 会让缓存失配 —— 之后形状不变
        时会被误跳过，表现为「光标卡在旧形状上」。目前全文件只有这一处。
        """
        if cursor != self._cursor:
            self._cursor = cursor
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
        # 两扇问话窗都跟着一起收掉。它们要是留着，Tk 的 mainloop 还转，
        # 程序就变成「窗口都没了但进程还在」—— 用户只会以为退出失败。
        #
        # 收关机那扇时**不当作「取消」**（不写 cancelled_at —— 用户退的是
        # 程序，不是拒绝关机），但也不再接着执行：下次启动时
        # _settle_shutdown_after_restart 会把这件没办完的事记成「错过」。
        self._close_shutdown_window()
        self._close_alert_window()
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
        # 归零之后不再按档位寄。那些档位讲的都是「还剩几天」，拿已经过去的
        # 时刻硬套档位，只会寄出一封「剩余负几天」的糊涂信（目标归零后被
        # 钉成过去的那一刻 —— 见 _latch_zero —— 这条路从此走得通，必须挡住）。
        # 归零这件事本身有界面闪字和关机确认窗在管，不归传书管。
        if remaining <= 0:
            return
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

        # 把「数据目录在哪」明确告诉发信进程 —— 它靠这个找到那两个信箱文件。
        #
        # 不能指望它自己猜：演练时主程序的数据目录是隔离目录，
        # 发信进程必须指向同一个地方，才可能取到任务、把结果交回来。
        env = dict(os.environ)
        env["ANCIENT_COUNTDOWN_HOME"] = DATA_DIR
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
            # 不是传书提醒那一套的结果：看看是不是窗口盯守寄出去的。
            # 两条路共用一个发信进程、一个结果值，只有 token 长什么样不同，
            # 所以在这里分流一次就够了 —— 不合这个 token 的当垃圾丢掉。
            self.collect_alert_result(token, data)
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

    # ---------------- 定时关机（时刻取自网址或设置文件）----------------
    #
    # 流程一句话讲清：
    #   网址 → （后台线程）取回一串日期数字 → 解析成时刻 → 成为**关机时刻**
    #   → 到点 → 弹确认窗 → 发关机命令（留一段缓冲可取消）
    #
    # 关机时刻还有第二个来处：**设置文件里写死的 shutdown.at**（远程设置 /
    # 共用设置那份文件带上它即可）。用户只维护一份配置文件 —— 反正远程设置
    # 也会定时下载，关机时刻写在里面，各台机器取回来就排上，不必再单独
    # 维护一个返回日期数字的网址。两条路喂的是同一个 self.shutdown_at，
    # 重启后以文件里的值为准（见 _restore_shutdown_at）。
    #
    # 为什么时刻可以由网址/文件说了算，而不是让用户在本机填：那头随时会改，
    # 改完这边不用动；填死一个时刻的话，每次改都得跑到这台机器上来改。
    #
    # ⚠️ 关机时刻与 self.target（用户倒计时目标）是两个变量，绝不合并 ——
    # 取一次数就把用户设的日子换掉，是 v1.6 犯过的错。

    def shutdown_cfg(self):
        return self.cfg.get("shutdown") or {}

    def site_fetch_tick(self, now):
        """该不该去取一次日期。绝大多数秒只是一次时间戳比较。"""
        cfg = self.shutdown_cfg()
        if not (cfg.get("url") or "").strip() or not cfg.get("auto_fetch"):
            return
        if self._site_fetching:
            return
        if now.timestamp() < self._site_next_at:
            return
        # 取一次。取完 _site_fetched 会把下次的时间重新排上：
        # refresh_hours 是几就隔几小时，是 0 就这一轮不再取（= 只在启动时取一次）。
        self.fetch_site_now(manual=False)

    def fetch_site_now(self, manual=False, url=None, done=None):
        """
        去用户自己的网站取那一串日期数字。返回 None 表示已经派出去，
        返回字符串表示当场就没法取（没填网址、上一次还没回来）。

        联网一律走后台线程：这一趟最长可能等 12 秒，放在主线程里就是
        「倒计时卡住 12 秒不动」。取回之后经 root.after 回到主线程落地 ——
        Tk 的对象只能在主线程碰。
        """
        import threading
        url = (url if url is not None
               else (self.shutdown_cfg().get("url") or "")).strip()
        if not url:
            return "还没填网址"
        if self._site_fetching:
            return "上一次还在取，稍等一下"
        self._site_fetching = True

        def work():
            try:
                dt, raw, err = fetch_site_target(url)
            except Exception as exc:                  # noqa: BLE001
                dt, raw, err = None, "", "取的时候出了岔子：%s" % exc
            try:
                self.root.after(0, lambda: self._site_fetched(
                    url, dt, raw, err, manual, done))
            except tk.TclError:
                pass                                  # 程序正在退出，不用落地了

        threading.Thread(target=work, daemon=True).start()
        return None

    def _site_fetched(self, url, dt, raw, err, manual, done):
        """取回来了（在主线程里跑）。"""
        self._site_fetching = False
        try:
            hours = float(self.shutdown_cfg().get("refresh_hours") or 0)
        except (TypeError, ValueError):
            hours = 0.0
        self._site_next_at = time.time() + (hours * 3600 if hours > 0
                                            else float("inf"))
        note = err or ""
        applied = False

        # 取回来的时刻比现在早 —— 网站那头的数字是旧的（或者干脆写错了）。
        # 这种时刻绝不采用：真当成关机时刻，程序下一秒就会判定「到点了」
        # 而把机器关掉。宁可什么都不改，把原话讲给用户。
        if dt is not None and dt <= datetime.datetime.now():
            err = "取到的时刻已经过去了（%s），没有采用" % pretty_target(dt)
            dt = None
            note = err

        if dt is not None:
            applied, why = self.apply_shutdown_at(dt)
            if applied:
                note = "取到「%s」→ 关机时刻定在 %s（倒计时目标没动）" % (
                    (raw or "").strip()[:40], pretty_target(dt))
            else:
                err = why
                note = why

        # 注意这里那个 "target" 键存的是**关机时刻**，不是倒计时目标
        # （名字沿用下来了，改它会让老注册表里的记录读不到；读取处见
        # _restore_shutdown_at）。
        self.site_date = {"at": _stamp(), "at_ts": time.time(), "url": url,
                          "raw": (raw or "")[:SITE_RAW_KEEP], "ok": bool(applied),
                          "target": canonical_target(dt) if applied else "",
                          "note": note, "auto": not manual}
        reg_store_write(SITE_STATE_KEY, self.site_date)
        if manual:
            self.set_notify_note("取关机时间：" + (note or "好了"))
        if done:
            try:
                done(dt, err)
            except Exception:                          # noqa: BLE001
                pass

    # ---- 远程设置 ----

    def remote_cfg(self):
        """远程设置这一段。缺的键用默认值补齐，免得调用处到处判 None。"""
        cfg = self.cfg.get("remote")
        if not isinstance(cfg, dict):
            cfg = {}
        return dict(DEFAULT_CONFIG["remote"], **cfg)

    def remote_items(self):
        """当前要同步哪些项（{} = 用默认那套）。"""
        picked = self.remote_cfg().get("items")
        base = default_remote_selection()
        if isinstance(picked, dict):
            for key in base:
                if key in picked:
                    base[key] = bool(picked[key])
        return base

    def remote_fetch_tick(self, now):
        """该不该去拉一次远程设置。绝大多数秒只是一次时间戳比较。"""
        cfg = self.remote_cfg()
        if not cfg.get("enabled") or not (cfg.get("url") or "").strip():
            return
        if self._remote_fetching or now.timestamp() < self._remote_next_at:
            return
        self.fetch_remote_now(manual=False)

    def fetch_remote_now(self, manual=False, done=None):
        """
        去远处把设置拉回来。返回 None 表示已经派出去，返回字符串表示当场
        就没法拉（没填网址、上一次还没回来）。

        和取关机时刻一样，联网走后台线程 —— 这一趟最长等 20 秒，
        放在主线程里就是「倒计时僵在那里 20 秒」。
        """
        import threading
        cfg = self.remote_cfg()
        url = (cfg.get("url") or "").strip()
        if not url:
            return "还没填网址"
        if self._remote_fetching:
            return "上一次还在拉，稍等一下"
        self._remote_fetching = True
        auth = cfg.get("auth") or "none"
        user = cfg.get("user") or ""
        secret = dict(self.secret or {})
        items = self.remote_items()

        def work():
            ok, err = False, ""
            try:
                bundle, err = fetch_remote_config(url, auth, user, secret)
                if bundle is not None:
                    ok, why = apply_remote_config(bundle, items)
                    err = "" if ok else why
            except Exception as exc:                  # noqa: BLE001
                ok, err = False, "拉的时候出了岔子：%s" % exc
            try:
                self.root.after(0, lambda: self._remote_fetched(
                    ok, err, manual, done))
            except tk.TclError:
                pass                                  # 程序正在退出，不用落地了

        threading.Thread(target=work, daemon=True).start()
        return None

    def _remote_fetched(self, ok, err, manual, done):
        """拉回来了（在主线程里跑）。"""
        self._remote_fetching = False
        try:
            hours = float(self.remote_cfg().get("refresh_hours") or 0)
        except (TypeError, ValueError):
            hours = 0.0
        self._remote_next_at = time.time() + (hours * 3600 if hours > 0
                                              else float("inf"))
        note = "已按远端的那份设置更新" if ok else (err or "没拉到")

        if ok:
            # 拉回来的可能改了配色、窗口尺寸、盯守设置……得整个重读一遍，
            # 否则界面还按旧设置画着，用户会以为「拉了但没生效」。
            self.reload_from_store()

        cfg = self.remote_cfg()
        cfg["last_at"] = _stamp()
        cfg["last_ok"] = bool(ok)
        cfg["last_note"] = note
        self.cfg["remote"] = cfg
        save_config(self.cfg)

        if manual:
            self.set_notify_note("远程设置：" + note)
        if done:
            try:
                done(ok, err)
            except Exception:                          # noqa: BLE001
                pass

    def fetch_remote_with(self, cfg, creds, done=None):
        """
        用**给定**的配置与凭据拉一次（试拉专用，不落盘）。

        给设置面板的「现在就拉一次」用：用户可能只是改了个网址、想先试试
        通不通，通了他才保存。所以这条路读的是面板上刚填的值，而不是盘上
        那份 —— 否则「试一下」要么得先保存，要么试的还是旧地址，两头都不对。

        返回 None 表示已经派出去；返回字符串表示当场就没法拉。
        """
        import threading
        url = (cfg.get("url") or "").strip()
        if not url:
            return "还没填网址"
        if self._remote_fetching:
            return "上一次还在拉，稍等一下"
        self._remote_fetching = True
        secret = dict(self.secret or {})
        secret.update(creds or {})
        items = self.remote_items()

        def work():
            ok, err = False, ""
            try:
                bundle, err = fetch_remote_config(url, cfg.get("auth") or "none",
                                                  cfg.get("user") or "", secret)
                if bundle is not None:
                    ok, why = apply_remote_config(bundle, items)
                    err = "" if ok else why
            except Exception as exc:                  # noqa: BLE001
                ok, err = False, "拉的时候出了岔子：%s" % exc
            try:
                self.root.after(0, lambda: self._remote_tried(ok, err, done))
            except tk.TclError:
                pass                                  # 程序正在退出

        threading.Thread(target=work, daemon=True).start()
        return None

    def _remote_tried(self, ok, err, done):
        """
        试拉的结果回来了。

        注意「试一下」其实也会真的把设置写进去（apply_remote_config 就是
        干这个的），所以成功之后界面得跟着刷新 —— 只弹一句「成功了」
        而屏幕上的配色纹丝不动，反而更让人糊涂。
        """
        self._remote_fetching = False
        if ok:
            self.reload_from_store()
        if done:
            try:
                done(ok, err)
            except Exception:                          # noqa: BLE001
                pass

    def remote_status_text(self):
        """设置面板上那行小字：上次拉成没成、什么时候。"""
        cfg = self.remote_cfg()
        at = (cfg.get("last_at") or "").strip()
        if not at:
            return "还没拉过"
        when = at[:16]
        if cfg.get("last_ok"):
            return "%s 成功" % when
        return "%s 失败：%s" % (when, (cfg.get("last_note") or "")[:60])

    def _restore_shutdown_at(self):
        """
        把关机时刻读回来（重启程序后接着用）。两个来处，**设置文件里写的优先**：

          ① cfg["shutdown"]["at"] —— 远程设置 / 共用设置那份文件里直接指定的时刻。
             用户只维护一份配置文件（远程设置本来就会定时下载），关机时刻写在
             里面即可，不必再单独维护一个返回日期数字的网址。
          ② site_date 里那份「已采用」的记录 —— 网址取回那条路的落点。

        为什么文件优先：文件是用户此刻明确写下的值；site_date 只是「上次网址
        取到了什么」的历史记录。两份都在时（既用网址又用设置文件），重启以文件
        为准；运行期内网址取到新值会当场覆盖（apply_shutdown_at），下次重启
        又回到文件那一份 —— 两条路喂的是同一个 self.shutdown_at。

        文件里那个时刻读不通（手写坏了）时当没写，继续看 site_date，不报错。
        两份都读不出、或记录本身标着没采用，就当没有关机时刻 ——
        宁可这次不关，也绝不凭空猜一个。
        """
        text = ((self.cfg.get("shutdown") or {}).get("at") or "").strip()
        if text:
            dt, _err = parse_target(text)
            if dt is not None:
                return dt
        info = self.site_date if isinstance(self.site_date, dict) else {}
        if not info.get("ok"):
            return None
        text = (info.get("target") or "").strip()
        if not text:
            return None
        dt, _err = parse_target(text)
        return dt

    def apply_shutdown_at(self, dt):
        """
        把取到的时刻落成**关机时刻**。返回 (是否已采用, 说明)。

        网址取回那条路走这里（_site_fetched 调它）。设置文件那条路
        （cfg["shutdown"]["at"]）不走这里 —— 它经 reload_from_store →
        _restore_shutdown_at 直接落 self.shutdown_at（reload 时 _armed_keys
        整个重置，效果一样）。

        这里刻意**不碰** self.cfg["target"] 与 self.target。
        那个是用户自己设的倒计时目标，和「这台机器几点关」是两件事；
        跑去网站取一次数就把人家设的日子换掉，是 v1.6 犯过的错。
        """
        self.shutdown_at = dt
        # 换了一个远程时刻 = 换了一件事：把「已经亲眼见过它还没到」的记号作废。
        # 不作废的话，新时刻会被旧记号带着直接通过准入检查 ——
        # 而它很可能根本就是个已经过去的时刻。
        self._armed_keys = set(k for k in self._armed_keys
                               if not k.startswith("remote|"))
        self._refresh_menu()
        return True, ""

    # ---- 两个来源，谁先到谁关 ----

    def shutdown_candidates(self):
        """
        当前算数的关机时刻，按时间从早到晚排好。

        返回 [(时刻, 来源, 身份证)]；一个来源都算不出来就是空表。
        这里**不管**「这件事办过没有」—— 那是调用方的事（见 shutdown_tick）。

        关机总开关关着的时候仍然照算：面板上要能显示「按几点关」，
        不然用户勾上开关之前什么都看不到。
        """
        cfg = self.shutdown_cfg()
        out = []
        if self.shutdown_at is not None:
            out.append((self.shutdown_at, "remote",
                        shutdown_key_of("remote", self.shutdown_at)))
        if cfg.get("from_target", True) and self.target is not None:
            out.append((self.target, "target",
                        shutdown_key_of("target", self.target)))
        out.sort(key=lambda item: item[0])
        return out

    def shutdown_next(self):
        """
        还没处理过的、最先到的那一个。返回 (时刻, 来源)；没有就 (None, None)。

        面板上那行「当前会按几点关」用它 —— 已经取消掉或者已经办过的那次
        不该继续挂在上面报时，否则用户会以为关机还排着。
        """
        done = (self.shutdown_state or {}).get("target_key") or ""
        for dt, src, key in self.shutdown_candidates():
            if key != done:
                return dt, src
        return None, None

    def shutdown_left_text(self):
        """
        还剩多久关机，一句人话。没排上 / 已经过去 / 办过了都直说。

        自己拼而不用 `_human_delta`：那个写的是「3 时 20 分」，主界面里当配角没问题，
        但这里是用户唯一能确认「到底定没定上、还有多久」的一行，得一眼看懂。
        """
        dt, src = self.shutdown_next()
        if dt is None:
            if (self.shutdown_state or {}).get("target_key"):
                return "这一次已经处理过了（换一下目标时刻才会再排）"
            return "还没有关机时刻"
        label = dict(SHUTDOWN_SOURCES).get(src, src)
        left = (dt - datetime.datetime.now()).total_seconds()
        if left <= 0:
            return "%s已到（%s）" % (label, pretty_target(dt))
        parts = []
        days = int(left // 86400)
        hours = int(left % 86400 // 3600)
        minutes = int(left % 3600 // 60)
        if days:
            parts.append("%d 天" % days)
        if hours or days:
            parts.append("%d 小时" % hours)
        if minutes or hours or days:
            parts.append("%d 分" % minutes)
        parts.append("%d 秒" % int(left % 60))
        return "%s %s（还有 %s）" % (label, pretty_target(dt), " ".join(parts))

    def shutdown_armed(self):
        """这次关机正在推进中：确认窗开着，或者命令已经发了正等结果。"""
        return (self.shutdown_state or {}).get("phase") in ("asking", "retrying")

    def shutdown_tick(self, now):
        """
        两个来源谁先到谁关。绝大多数秒只做几次时间比较。

        一次 tick 只推进一件事，按优先级：
          ① 重试档  —— 命令已经发过，看是不是该再试一次了
          ② 确认档  —— 窗还开着，等它自己回调，这里什么都不做
          ③ 新触发  —— 有别扭的时刻到了，弹确认窗（这才是真正罕见的那一步）

        触发用的是 self.shutdown_at 与 self.target 里**先到的那个**，
        两者仍然是各自独立的变量，谁也不改写谁。
        """
        cfg = self.shutdown_cfg()
        if not cfg.get("enabled"):
            return

        st = self.shutdown_state
        phase = st.get("phase") or ""

        # ① 命令已经发出去过：等够一分钟再看。程序如果还在跑，就说明
        #    机器没关成（关成了这个进程早就随系统没了），于是再发一次。
        if phase == "retrying":
            if time.time() < float(st.get("next_try") or 0):
                return
            self._shutdown_fire(st)
            return

        # ② 确认窗开着：一切等窗口那边的回调说了算。
        #    但窗口可能已经不在了（程序重启过，或者被系统关掉了）——
        #    那种情况下 phase 会永远卡在 asking，机器再也关不掉，
        #    所以这里负责保证窗还立着。
        if phase == "asking":
            self.ensure_shutdown_window()
            return

        cands = self.shutdown_candidates()
        if not cands:
            return

        # 亲眼见过「它还没到」的时刻才允许关。这是关机的准入条件：
        # 程序不在运行的那段时间里时刻悄悄过去了（关机三天后开机就是这种），
        # 那种时刻**绝不能补关** —— 用户晚上设了 12 点关机，第二天一开机
        # 就被关掉，他只会以为电脑坏了。
        # 每个时刻各记各的：远程那个刚换过、本地那个早就见过，互不牵连。
        for cand_dt, _src, cand_key in cands:
            if now < cand_dt:
                self._armed_keys.add(cand_key)

        done = st.get("target_key") or ""
        due = [c for c in cands if c[0] <= now and c[2] != done]
        if not due:
            return
        dt, src, key = due[0]            # 已经按时刻排过序，第一个就是最先到的

        if key not in self._armed_keys:
            st.update({"target_key": key, "source": src, "phase": "",
                       "fired_at": "", "cancelled_at": "", "tries": 0,
                       "next_try": 0, "missed_at": _stamp(),
                       "note": "%s（%s）在程序没运行的时候过去了，没有补关机"
                               % (dict(SHUTDOWN_SOURCES).get(src, src),
                                  pretty_target(dt))})
            save_shutdown_state(st)
            self.set_notify_note(st["note"])
            return

        # 到了，而且确实看着它走过来 —— 开始处理这一件事：先弹窗问一句。
        # 这里就把 target_key 记上：它一变才代表「换了一件事」，
        # 所以同一件事永远不会走到这一步第二遍。
        st.update({"target_key": key, "source": src, "phase": "asking",
                   "fired_at": "", "cancelled_at": "", "missed_at": "",
                   "tries": 0, "next_try": 0, "note": ""})
        save_shutdown_state(st)
        self._open_shutdown_alert(dt, src)

    def _shutdown_fire(self, st):
        """
        真发一次关机命令。**发出去不等于关成了** —— 一分钟后再看：
        这个进程还在，就说明机器没关，接着试（见 shutdown_tick 的第①档）。

        不设「试够几次就算失败」的上限：用户要的就是「没关成就一直试」。
        重试期间不再弹窗，只在界面上留一行状态，免得每分钟骚扰一次。
        """
        ok, err = run_shutdown(0)
        tries = int(st.get("tries") or 0) + 1
        st["tries"] = tries
        st["phase"] = "retrying"
        st["next_try"] = time.time() + SHUTDOWN_RETRY_SEC
        if ok:
            st["fired_at"] = st.get("fired_at") or _stamp()
            st["note"] = ("已发出关机命令（第 %d 次）。%d 秒后还关不掉就再试一次。"
                          % (tries, SHUTDOWN_RETRY_SEC))
        else:
            st["note"] = ("关机命令没发出去（第 %d 次）：%s。%d 秒后再试。"
                          % (tries, err, SHUTDOWN_RETRY_SEC))
        save_shutdown_state(st)
        self._refresh_menu()
        self.set_notify_note(st["note"])

    def _open_shutdown_alert(self, when, source):
        """弹「马上要关机」那扇窗。已经开着一扇就先把它顶到前面来。"""
        win = getattr(self, "_shutdown_win", None)
        if win is not None and win.alive():
            win.lift()
            return
        try:
            self._shutdown_win = ShutdownAlertWindow(
                self, when, source, self._shutdown_wait_sec())
        except Exception as exc:                  # noqa: BLE001
            # 窗都弹不出来就不能装作问过了 —— 当作「没人反对」，直接关。
            # 否则这台机器永远不会关，而用户以为已经排上了，比误关更糟。
            log_problem("关机确认窗", type(exc), exc, exc.__traceback__)
            self._shutdown_win = None
            self.shutdown_alert_done(True)

    def _shutdown_wait_sec(self):
        """确认窗等多少秒。配置里那个数可能被人手改坏，这里兜住。"""
        try:
            wait = int(float(self.shutdown_cfg().get("grace_sec",
                                                     SHUTDOWN_GRACE_DEFAULT)))
        except (TypeError, ValueError):
            wait = SHUTDOWN_GRACE_DEFAULT
        return max(0, min(wait, SHUTDOWN_GRACE_MAX))

    def _shutdown_key_time(self):
        """把 state 里记着的那个时刻解回 datetime。解不出（数据被人手改过）返回 None。"""
        key = (self.shutdown_state or {}).get("target_key") or ""
        if "|" not in key:
            return None
        try:
            return datetime.datetime.strptime(key.split("|", 1)[1],
                                              "%Y-%m-%dT%H:%M:%S")
        except ValueError:
            return None

    def ensure_shutdown_window(self):
        """
        确认档里保证那扇窗立着。

        程序重启过一次的话窗已经不在了，而 phase 还写着 asking ——
        不补弹的话这台机器就再也关不掉了，界面上却显示「等你表态」。
        """
        win = getattr(self, "_shutdown_win", None)
        if win is not None and win.alive():
            return
        if win is not None:
            win.close()
        dt = self._shutdown_key_time()
        if dt is None:
            # 时刻都解不出来了（数据被手改坏），退回空闲按正常路径重新判一次。
            st = self.shutdown_state
            st["phase"] = ""
            save_shutdown_state(st)
            return
        self._open_shutdown_alert(dt, self.shutdown_state.get("source") or "remote")

    def _settle_shutdown_after_restart(self):
        """
        程序启动时，把上一轮遗留的「进行中」收尾成「错过」。

        确认窗开着、命令发了正等重试 —— 这两档都只活在**这一轮运行**里。
        程序重启说明中间断过一次，而断过就绝不补关（同 shutdown_tick 里
        那条准入线）。用户想拦下一次关机，最顺手的动作就是重启程序或者
        直接退出，这时候回头再给他关掉，是最不能接受的一种。
        """
        st = self.shutdown_state
        if not st.get("phase"):
            return
        st["phase"] = ""
        st["next_try"] = 0
        if st.get("fired_at"):
            st["note"] = "程序重启过，不再接着重试关机"
        else:
            st["missed_at"] = _stamp()
            st["note"] = "程序重启过，这次关机没有接着执行"
        save_shutdown_state(st)

    def _close_shutdown_window(self):
        win = getattr(self, "_shutdown_win", None)
        self._shutdown_win = None
        if win is not None:
            win.close()

    def shutdown_alert_done(self, proceed, drill=False):
        """
        确认窗那边回来了。proceed=True 就是「该关了」。

        演练走这条路只有一句话，**一个字都不改 state** ——
        试一次就把真事标记成「办过了」的话，用户等于用演练把功能关掉了。
        """
        self._shutdown_win = None
        if drill:
            self.set_notify_note("演练结束：" + ("真关机的话，刚才那一刻就该关了。"
                                                if proceed else
                                                "你点了「先不关」，什么都不会发生。"))
            return
        st = self.shutdown_state
        if not proceed:
            st.update({"phase": "", "next_try": 0, "cancelled_at": _stamp(),
                       "note": "你在关机确认窗里点了「先不关」，这一次不执行"})
            save_shutdown_state(st)
            self._refresh_menu()
            self.set_notify_note(st["note"])
            return
        self._shutdown_fire(st)

    def shutdown_drill(self):
        """
        试一遍：真弹那扇窗、真倒计时，但**不会真关机**。

        为什么要有它：关机默认要等到某一天才可能发生，用户点完保存
        「屏幕上什么都不会发生」，等于没法验证。凡是「要等很久才可能
        发生」的功能，都得给一个「现在就看」的入口。
        """
        win = getattr(self, "_shutdown_win", None)
        if win is not None and win.alive():
            win.lift()
            return "关机确认窗已经开着了"
        cfg = self.shutdown_cfg()
        # 拿哪个来源演练：优先拿用户真开着的那条路，两条都关就拿倒计时那个。
        if cfg.get("from_target", True) and self.target is not None:
            src, when = "target", self.target
        else:
            src = "remote"
            when = self.shutdown_at or datetime.datetime.now()
        self._shutdown_win = ShutdownAlertWindow(
            self, when, src, self._shutdown_wait_sec(), drill=True)
        return None

    def shutdown_cancel_now(self):
        """
        取消正在推进的这次关机（右键菜单那一项）。返回给用户看的一句话。

        两个档位都得停得住：确认窗开着的（把窗收掉），以及命令已经发出去、
        正等着重试的（把重试停掉）。少停一个，用户就只能干看着机器被关。
        """
        st = self.shutdown_state
        self._close_shutdown_window()
        ok, err = cancel_shutdown()   # 系统那边万一还排着 /t 缓冲，一并撤掉
        if st.get("phase"):
            st["cancelled_at"] = _stamp()
            st["note"] = ("已取消这次关机" if ok else "取消关机失败：%s" % err)
        else:
            st["note"] = "没有正在进行的关机"
        st["phase"] = ""
        st["next_try"] = 0
        save_shutdown_state(st)
        self._refresh_menu()
        self.set_notify_note(st["note"])
        return st["note"]

    # ---------------- 窗口盯守 ----------------
    #
    # 状态机只有三档，写清楚免得绕晕：
    #   waiting   还没看见过这扇窗。看见了就转 watching。
    #             「开机时游戏还没起来」就停在这一档 —— 一直看不见不算消失，
    #             否则每次开机都会白寄一封信。机器重启过也会被推回这一档
    #             （见 _disarm_watch_after_reboot）。
    #   watching  看见过、现在正盯着。某一趟看不见了就转 pending。
    #   pending   不见了，弹窗问「是你自己关的吗」，**同时每 30 秒核实一次
    #             它是不是真的还不在** —— 这就是「持续不在线十分钟才寄信」：
    #             这十分钟里它只要又出现过一次，就当场撤销（退回 watching），
    #             一封信都不寄。倒计时走完（它始终没再出现）就寄信。
    #             不论答没答，处理完都回到 waiting：窗口再出现时自动接着盯。
    #
    # 三档连同窗口名都写在数据文件里，所以重启程序之后接着盯，不需要重新选窗口。

    def watch_cfg(self):
        return self.cfg.get("watch") or {}

    def _watch_interval(self):
        """巡检间隔（秒）。写在设置里的是分钟。"""
        try:
            minutes = int(float(self.watch_cfg().get("interval_min") or 30))
        except (TypeError, ValueError):
            minutes = 30
        return max(WATCH_PROBE_MIN, min(minutes, WATCH_PROBE_MAX)) * 60

    def watch_reset(self, keyword, note=""):
        """换了一扇要盯的窗 = 换了一件事：状态机整个推倒，别把旧窗口的历史带过来。"""
        st = self.watch_state
        st.update({"phase": "waiting" if keyword else "off", "keyword": keyword,
                   "seen_at": "", "seen_boot": 0.0, "rounds": 0,
                   "last_probe": 0.0, "pend_probe": 0.0, "pending": {},
                   "note": note or ("等「%s」出现" % keyword if keyword else "")})
        save_watch_state(st)
        self._close_alert_window()

    def _disarm_watch_after_reboot(self):
        """
        程序启动时：机器重启过 → 把盯守状态推回「等出现」（waiting）。

        为什么必须有这一条：盯守状态存在数据文件里，为的是重启程序接着盯。
        但「重启程序」和「重启机器」是两回事。机器重启之后，那扇窗往往还没
        起来（或者得用户手动开）—— 而状态里还留着上次的 watching，第一趟
        巡检就「发现窗口不见了」→ 弹窗 → 十分钟后寄信。每次开机都白寄一
        封信，就是这么来的（用户说的「刚开机的时候」）。

        怎么判断机器重启过：比开机时刻。开机毫秒数随开机归零，和墙上时钟
        一减就是「这次开机是几点」；状态里记着「上次看见那扇窗时的开机
        时刻」（seen_boot）。两个时刻不是同一次开机 → 这中间重启过 → 推倒。
        程序只是重启、机器没重启 → 原样保留（该弹的窗还会被
        ensure_alert_window 叫回来）。墙上时钟被调过几分钟也算「重启过」——
        那是往安全的方向错：最多晚一会儿寄信，不会白寄。
        """
        st = self.watch_state
        if st.get("phase") not in ("watching", "pending"):
            return
        seen_boot = st.get("seen_boot")
        if not isinstance(seen_boot, (int, float)) or seen_boot <= 0:
            seen_boot = None          # 升级上来的老状态没有这一笔：宁可推倒重来
        if seen_boot is None or abs(boot_at() - seen_boot) > WATCH_BOOT_DRIFT_SEC:
            st.update({"phase": "waiting", "pending": {}, "pend_probe": 0.0,
                       "last_probe": 0.0, "rounds": 0, "seen_at": "",
                       "seen_boot": 0.0,
                       "note": "机器重启过，等「%s」再出现"
                               % (st.get("keyword") or "")})
            save_watch_state(st)
            self._close_alert_window()

    def watch_tick(self, now):
        cfg = self.watch_cfg()
        keyword = (cfg.get("title") or "").strip()
        st = self.watch_state

        if not cfg.get("enabled") or not keyword:
            if st.get("phase") not in ("", "off"):
                st.update({"phase": "off", "note": "", "pending": {}})
                save_watch_state(st)
                self._close_alert_window()
            return

        if st.get("keyword") != keyword:
            self.watch_reset(keyword)
            return

        if st.get("phase") == "pending":
            # 问话窗开着。这时候**继续核实**那扇窗在不在 —— 这就是「持续
            # 不在线十分钟才寄信」：倒计时的每一分钟都要求它确实还不在，
            # 这中间它只要又出现过一次，就当场撤销，不当它消失过。
            # （早先的版本这十分钟是闭着眼数的：窗口回来了信照样寄。）
            clock = now.timestamp()
            if clock - float(st.get("pend_probe") or 0) >= WATCH_CONFIRM_SEC:
                st["pend_probe"] = clock
                if window_present(keyword):
                    # 它回来了：虚惊一场。不走 finish —— 那不是「用户确认
                    # 自己关的」，是窗口自己回来了，一封信都不该寄。
                    st.update({"phase": "watching", "pending": {},
                               "pend_probe": 0.0, "last_probe": clock,
                               "seen_at": _stamp(), "seen_boot": boot_at(),
                               "rounds": int(st.get("rounds") or 0) + 1,
                               "note": "它又出现了，虚惊一场，接着盯"})
                    save_watch_state(st)
                    # 只收真出事那扇窗：演练那扇（如果在演）走的是另一条
                    # 时间线，不该被真实盯守的撤销带走。
                    win = self._alert_win
                    self._alert_win = None
                    if win is not None:
                        try:
                            win.close()
                        except Exception:              # noqa: BLE001
                            pass
                    return
                save_watch_state(st)
            self.ensure_alert_window()
            return

        clock = now.timestamp()
        if clock - float(st.get("last_probe") or 0) < self._watch_interval():
            return
        st["last_probe"] = clock

        here = window_present(keyword)
        if st.get("phase") != "watching":
            # 还没盯上：这一趟要么「看见了，开始盯」，要么继续等。
            # 「从没见过」和「见过又没了」必须分开 —— 机器刚开机、游戏还没起来
            # 时一直看不见它，那时候发信纯粹是骚扰。
            st["phase"] = "watching" if here else "waiting"
            st["seen_at"] = _stamp() if here else ""
            if here:
                st["seen_boot"] = boot_at()  # 这次开机里见过它（重启判断靠这笔）
            st["rounds"] = 0
            st["note"] = ("已看到「%s」，开始盯守" % keyword) if here \
                else "还没看到这个窗口，等它出现"
            save_watch_state(st)
            return

        if here:
            st["rounds"] = int(st.get("rounds") or 0) + 1
            st["seen_boot"] = boot_at()      # 还在：刷新「本次开机见过它」
            st["note"] = "盯守中（第 %d 次确认它还在）" % st["rounds"]
            save_watch_state(st)
            return

        self.open_watch_alert(keyword)

    def watch_drill(self, keyword=None):
        """
        演练：假装那扇窗刚不见，把「弹窗问一句 → 到点自动寄信」整条路真走一遍。

        为什么非要有这个按钮：真实盯守按 interval_min 分钟才看一眼（默认半小时），
        用户勾完点「保存」之后屏幕上什么都不会发生 —— 他分不清是「配好了正在等」
        还是「配错了根本没在工作」。这个按钮让他几秒内看见全貌，包括那封信。

        刻意**不碰**真实状态机（watch_state）：演练要是把三档状态推来推去，
        用户回头看到的就是一份被搅过的盯守状态。所以演练的上下文单独拿着，
        走完也不写回去；那扇问话窗也另占一个槽（_drill_win），
        不与真出事的窗抢位置。
        """
        keyword = (keyword or "").strip() \
            or (self.watch_cfg().get("title") or "").strip() or "（演练用的窗口）"
        now = time.time()
        pend = {
            "at": _stamp(), "at_ts": now, "drill": True,
            "deadline_ts": now + WATCH_DRILL_SEC,
            "keyword": keyword,
            "minutes": WATCH_DRILL_SEC / 60.0,
            "seen_at": _stamp(),
            "interval_min": max(1, self._watch_interval() // 60),
            "id": "drill-%s-%d" % (_stamp("%H%M%S"), random.randint(100, 999)),
        }
        self._close_alert_window()
        self._drill_win = WatchAlertWindow(self, pend, drill=True)
        return True

    def open_watch_alert(self, keyword):
        """
        窗口不见了：先问一句「是你自己关的吗」，不立刻发信。

        无人值守时没人应答，倒计时走完照样寄出去 —— 默认是「寄」。
        这一句问话只在「有人恰好坐在机器前」时才起作用：他点一下就不寄了。

        倒计时的每一分钟都是**核实过它确实还不在**的（watch_tick 的 pending
        档每 30 秒看一眼）：这十分钟里它只要又出现过一次，问话窗就当场合掉。
        所以「等满十分钟」等于「连续十分钟确认它不在」，不是闭着眼数。
        """
        try:
            minutes = int(float(self.watch_cfg().get("grace_min") or 10))
        except (TypeError, ValueError):
            minutes = 10
        minutes = max(WATCH_GRACE_MIN, min(minutes, WATCH_GRACE_MAX))

        st = self.watch_state
        st["phase"] = "pending"
        st["pending"] = {
            "at": _stamp(), "at_ts": time.time(),
            "deadline_ts": time.time() + minutes * 60,
            "keyword": keyword, "minutes": minutes,
            "seen_at": st.get("seen_at") or "",
            "interval_min": self._watch_interval() // 60,
            "id": "%s-%d" % (_stamp("%H%M%S"), random.randint(100, 999)),
        }
        st["note"] = "窗口不见了，等你确认（%d 分钟）" % minutes
        save_watch_state(st)
        self.ensure_alert_window()

    def ensure_alert_window(self):
        """保证那扇问话窗立着。程序重启后也会被这一句叫回来（状态在注册表里）。"""
        win = self._alert_win
        if win is not None:
            try:
                if win.alive():
                    win.lift()
                    return
            except tk.TclError:
                pass
        self._alert_win = None
        st = self.watch_state
        if st.get("phase") != "pending" or not st.get("pending"):
            return
        self._alert_win = WatchAlertWindow(self, st["pending"])

    def _close_alert_window(self):
        """把两扇问话窗都收掉：真出事的那扇、以及演练那扇。"""
        for attr in ("_alert_win", "_drill_win"):
            win = getattr(self, attr, None)
            setattr(self, attr, None)
            if win is not None:
                try:
                    win.close()
                except Exception:                      # noqa: BLE001
                    pass

    def finish_watch_alert(self, send, pend=None):
        """
        那扇问话窗有结果了。send=True 就把信寄出去。

        真实盯守下，不论哪种结果，状态都退回 waiting：窗口下次再出现时
        自动接着盯 —— 这就是「下次该窗口出现时自动恢复检测」那一条。

        pend 传进来时按它办，并且**不碰状态机** —— 演练走的就是这条路，
        它只是演一遍，不该把真实的三档状态搅乱。
        """
        drill = bool((pend or {}).get("drill"))
        if pend is None:
            pend = dict((self.watch_state or {}).get("pending") or {})
        if not drill:
            # 只有真实盯守才动状态机：退回 waiting，窗口下次出现自动接着盯。
            st = self.watch_state
            st.update({"pending": {}, "phase": "waiting", "seen_at": "",
                       "seen_boot": 0.0, "rounds": 0, "last_probe": 0.0,
                       "pend_probe": 0.0})
            st["note"] = ("窗口消失，已寄信告知" if send
                          else "你确认是自己关的，没有寄信")
            save_watch_state(st)
        if drill:
            self._drill_win = None
        else:
            self._alert_win = None
        if not send:
            self.set_notify_note("盯守：" + ("演练到此为止，没有寄信" if drill
                                            else "你确认是自己关的，没有寄信"))
            return True
        return self.send_watch_mail(pend)

    def send_watch_mail(self, pend):
        """
        窗口消失的告警信。邮箱设置直接用「传书」里那一套 ——
        同一台机器上没有理由配两个发件邮箱。

        pend 里带 drill 的，是「试一遍」演练出来的：信照样真发（不真发就等于
        没测），但主题和正文都写明是演练 —— 否则用户收到一封「窗口不见了」
        却根本没出事，白白紧张一场，下次就不敢信这封信了。
        """
        drill = bool(pend.get("drill"))
        keyword = (pend.get("keyword") or self.watch_cfg().get("title")
                   or "（未命名窗口）")
        try:
            every = int(pend.get("interval_min") or 0) or (
                self._watch_interval() // 60)
        except (TypeError, ValueError):
            every = 30

        if drill:
            lines = [
                "这是一封演练信：你在设置面板里点了「试一遍」。",
                "那扇窗口并没有真的不见 —— 收到就不用管，说明链路是通的。",
                "",
            ]
        else:
            lines = ["你盯着的那扇窗口不见了。", ""]
        lines += [
            "窗口名称　%s" % keyword,
            "发现时间　%s" % (pend.get("at") or _stamp()),
            "上次见到　%s" % (pend.get("seen_at") or "—"),
            "检查间隔　每 %d 分钟看一眼" % every,
        ]
        if not drill:
            # 这十分钟不是闭着眼数的：问话期间每 30 秒核实一次，确实一直
            # 不在才走到寄信这一步。写进信里，收信的人才知道它有多确定。
            lines.append("连续不见　%d 分钟（期间反复确认过）"
                         % int(pend.get("minutes") or 10))
        sign = self.notify_signature()
        if sign:
            lines.append("寄出机器　%s" % sign)
        lines.append("（演练：真出这种事的时候，通知你的就是这封）" if drill
                     else "（连续 %d 分钟反复确认它不在，按无人值守的约定自动寄出）"
                          % int(pend.get("minutes") or 10))
        lines += self.mail_footer()
        body = "\n".join(lines)
        if len(body.encode("utf-8")) > NOTIFY_BODY_LIMIT:
            body = body.encode("utf-8")[:NOTIFY_BODY_LIMIT].decode("utf-8", "ignore")

        if not self.notify_configured():
            self.record_alert(pend, "", "failed", "邮箱还没配好")
            self.set_notify_note(("演练发不出去：" if drill else "窗口不见了，但")
                                 + "邮箱还没配好，没能寄信")
            return False

        token = "watch-%s-%d" % (_stamp("%H%M%S"), random.randint(100, 999))
        subject = "窗口不见了（演练）" if drill else "窗口不见了"
        ok, err = self._spawn_mailer(token, self.mail_subject(subject), body)
        if not ok:
            self.record_alert(pend, token, "failed", err)
            self.set_notify_note(("演练信没寄出去：" if drill else "窗口告警没寄出去：")
                                 + err)
            return False
        self.record_alert(pend, token, "sending", "")
        self.set_notify_note("正在寄演练信…" if drill else "窗口不见了，正在寄信告知…")
        return True

    def record_alert(self, pend, token, status, error=""):
        """盯守通知的寄信记录。只留最近 20 条 —— 注册表的值不能无上限地长。"""
        items = self.alert_state.setdefault("items", [])
        items.append({"token": token, "keyword": pend.get("keyword", ""),
                      "at": _stamp(), "at_ts": time.time(),
                      "status": status, "error": error,
                      "drill": bool(pend.get("drill"))})
        del items[:-20]
        save_alert_state(self.alert_state)

    def collect_alert_result(self, token, data):
        """发信进程交回来的结果，如果这一封是窗口告警就记到它的履历里。"""
        item = None
        for rec in self.alert_state.get("items", []):
            if rec.get("token") == token and rec.get("status") == "sending":
                item = rec
                break
        if item is None:
            return
        if data.get("ok"):
            item["status"] = "sent"
            item["error"] = ""
            item["sent_at"] = _stamp()
            self.set_notify_note("窗口告警已寄出")
        else:
            message = (data.get("error") or "未知错误").strip()
            item["status"] = "failed"
            item["error"] = message
            self.set_notify_note("窗口告警寄送失败：%s" % message[:48])
        save_alert_state(self.alert_state)

    def watch_status_text(self):
        """盯守现在到底是什么状况，一句人话（设置面板和传书记录都用它）。"""
        cfg = self.watch_cfg()
        st = self.watch_state
        if not cfg.get("enabled"):
            return "未开启"
        keyword = (cfg.get("title") or "").strip()
        if not keyword:
            return "还没选要盯的窗口"
        phase = st.get("phase")
        if phase == "watching":
            return "盯守中：%s（已确认还在 %d 次）" % (keyword, int(st.get("rounds") or 0))
        if phase == "pending":
            left = int(float((st.get("pending") or {}).get("deadline_ts") or 0)
                       - time.time())
            if left < 0:
                left = 0
            return "窗口不见了，问话窗还开着（还有 %d 分 %d 秒自动寄信，" \
                   "它再出现就撤销）" % (left // 60, left % 60)
        return "等「%s」出现" % keyword

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
                       autostart=None, notify_cfg=None, secret=None,
                       extra_cfg=None):
        err = None
        parsed, err = parse_target(target_text)
        if parsed is None:
            return err
        self.cfg["target"] = target_text.strip()
        self.cfg["thresholds"] = thresholds
        self.cfg["locked"] = bool(locked)
        self.cfg["always_on_top"] = bool(topmost)
        self.root.attributes("-topmost", bool(topmost))

        # 定时关机 / 窗口盯守这两块整体由面板拼好递进来，这里只合并落盘
        # （签名已经很长了，再加七八个参数更没法看）。
        #
        # 但有一件事必须在这里做：「要盯哪扇窗」变了，状态机就得推倒重来。
        # 不推倒的话，旧窗口的「已确认它在」会算到新窗口头上 ——
        # 换了窗口却还停在 watching，新窗口一次都没看见就报「不见了」。
        if extra_cfg:
            old_watch = ((self.cfg.get("watch") or {}).get("title") or "").strip()
            self.cfg = deep_merge(self.cfg, extra_cfg)
            new_watch = ((self.cfg.get("watch") or {}).get("title") or "").strip()
            if old_watch != new_watch:
                self.watch_reset(new_watch, "刚换了要盯的窗口，重新开始")
        # 这里刻意不重置 _armed_keys：改别的设置（配色、邮箱、要盯的窗口）
        # 不该影响「我是不是亲眼见过那个时刻还没到」这条准入线。
        # 关机时刻真的换了的时候，apply_shutdown_at 自己会把那一条挑出去。
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
        self._zero_latched = False     # 换了时刻就是新的一轮归零
        self._last_text = None
        self.theme = None
        self._last_notify_check = 0.0      # 让下一轮巡检立刻用新设置重算一次
        self.layout()
        return None

    def _latch_zero(self):
        """
        归零的第一帧：把目标时刻钉成带年份的写法，落盘。

        为什么要钉 —— 不带年份的目标（10.10）一旦过期，parse_target 会把它
        顺到「明年的同一天」（那是给「设置的时候还没到」准备的规则）。于是
        倒计时明明已经归零，重启一次程序（或者到点关机后再开机），界面就从
        「時辰已到」变成「还剩三百多天」。在归零那一刻把解析出的那一刻
        （含年份）写回配置，之后无论重启多少次，读到的都是过去的那一刻，
        界面老老实实停在归零态，等用户按「+30 天」或自己改时刻。

        只改写法、不改时刻：关机 / 传书两边认的还是同一个时刻（身份证没变）。
        一轮归零只钉一次（_zero_latched），落盘失败也不再重试 —— 每秒重试
        只会往日志里灌错误，用户改一次目标随时能重来。
        """
        self._zero_latched = True
        if self.target is None:
            return
        frozen = target_text_of(self.target)
        if str(self.cfg.get("target") or "").strip() == frozen:
            return                          # 已经是钉过的写法，一个字都不用动
        self.cfg["target"] = frozen
        try:
            save_config(self.cfg)
        except Exception as exc:                      # noqa: BLE001
            log_problem("归零钉时刻", type(exc), exc, exc.__traceback__)

    def extend_target_days(self, days=30):
        """
        一键把倒计时往后顺延 N 天（右键菜单第一项、设置面板的「＋30 天」，
        两处共用这一个方法）。返回 None 表示成功，字符串是给界面看的原因。

        规则（用户点名要的）在 extend_target_text 里：没过期在原时刻上加，
        过期了从现在起算。这里负责把结果落进配置、刷新界面，以及三件
        顺手必须做的事：

        · 关机正在推进时（确认窗开着 / 命令已发在重试）点 +30 天，意思
          必然是「这次不关了」—— 先把那一档停掉再改时刻。不停的话确认窗
          还挂着等回调，机器照样会被关。
        · 设置面板开着的话，同步面板上的输入框 —— 不然用户接着点「保 存」，
          会拿框里的旧文本把刚顺延的时刻又改回去。
        · 时刻换了，传书巡检下一轮立刻按新时刻重算（老目标排下的提醒作废）。
        """
        now = datetime.datetime.now()
        text = extend_target_text(self.cfg.get("target"), days=days, now=now)
        parsed, perr = parse_target(text, now)
        if parsed is None:
            # 自己生成的文本自己读不回，理论上来不到这一步；真来了就原地不动，
            # 绝不能把一个解析不了的目标写进配置（那会让整个窗口变成报错态）。
            return "生成的新时刻解析失败（%s），目标保持原样" % perr
        if self.shutdown_armed():
            self.shutdown_cancel_now()
        self.cfg["target"] = text
        save_config(self.cfg)
        self.target = parsed
        self.parse_err = None
        self.remaining = (self.target - now).total_seconds()
        self.zero_mode = self.remaining <= 0
        self._zero_latched = False         # 新的一轮，跟运行中归零互不相干
        self._last_text = None
        self.theme = None
        self._last_notify_check = 0.0
        self.layout()
        self._refresh_menu()
        panel = self._settings
        if panel is not None:
            try:
                panel.refresh_target_entry()
            except Exception:                        # noqa: BLE001
                pass                     # 面板正在关之类的小岔子，不值得管
        self.set_notify_note("已顺延 %d 天 → %s" % (days, pretty_target(self.target)))
        return None

    def factory_reset(self):
        """
        恢复出厂设置：清掉注册表里的数据键，并把内存、窗口、界面一起打回「刚装好」。

        清理范围（都在同一个数据键里，一个键装了全部）：
          目标时刻 / 颜色规则 / 配色 / 邮箱与授权码 / 寄信履历 / 窗口位置与大小 /
          定时关机的网址 / 窗口盯守的设置与状态。
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
        self._zero_latched = False
        self._last_text = None
        self.theme = None
        self.blink = False
        self._last_notify_check = 0.0        # 让下一轮巡检立刻用新设置重算
        self._notify_note = ""
        self._notify_note_at = 0.0
        # 盯守与关机的状态也在那个数据键里，已经被删了 ——
        # 内存里那份必须跟着归零，否则界面还显示着「盯着某某游戏」，
        # 而注册表里已经什么都没有，用户再点一次保存才可能对上。
        self.site_date = {}
        self.shutdown_state = load_shutdown_state()
        self.watch_state = load_watch_state()
        self.alert_state = load_alert_state()
        self.shutdown_at = None          # 网址也清掉了，自然没有关机时刻
        self._armed_keys = set()
        self._close_shutdown_window()
        self._close_alert_window()

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
        # 盯守与关机的状态也一并重读：共用设置文件可能把「盯哪扇窗」「关机网址」
        # 整个换掉，只换配置不换状态的话，两边的窗口名就对不上了
        # （对不上的后果由 watch_tick 兜住：它会当场把状态机推倒重来）。
        self.shutdown_state = load_shutdown_state()
        self.watch_state = load_watch_state()
        self.alert_state = load_alert_state()
        self.site_date = reg_store_read(SITE_STATE_KEY, {})
        if not isinstance(self.site_date, dict):
            self.site_date = {}
        # 关机时刻跟着重读：共用设置文件可能把网址整个换掉，
        # 那种情况下旧的关机时刻就不再作数了。
        self.shutdown_at = self._restore_shutdown_at()

        self.target, self.parse_err = parse_target(self.cfg.get("target"))
        self.remaining = ((self.target - datetime.datetime.now()).total_seconds()
                          if self.target else None)
        self.zero_mode = bool(self.remaining is not None and self.remaining <= 0)
        self._zero_latched = False     # 换过设置重新算，归零的第一帧会再钉一次
        self._last_text = None
        self.theme = None
        self.blink = False
        self._armed_keys = set()            # 换过设置，关机那条准入线重新走一遍
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
    挑「带哪几项」的那个小窗。

    为什么非得有它：用户要同步的是十几台机器，绝大多数设置想配成一样，
    偏偏每台机器的目标时刻各不相同（各有各要倒计的事）。不挑的话，一次
    同步就把所有机器的时刻冲成同一个 —— 恰是他最不能接受的事。
    所以默认把「目标时刻」留成不勾，其余全勾；想连时刻一起发，自己点上。

    两处在用，所以项目表与落地动作都是参数传进来的，没写死：
      · 导出共用设置 —— 挑完写文件，勾选记在本机（下次还是这套）
      · 远程设置 —— 挑「从网址取回来的那份，认哪几项」，勾选写回配置
    """

    W = 440

    def __init__(self, app, on_pick, specs=None, current=None, title=None,
                 note=None, persist=None):
        self.app = app
        self.on_pick = on_pick
        self.specs = list(specs) if specs is not None else list(SHARED_ITEMS)
        self.sel = dict(current) if current is not None else load_shared_selection()
        self.title = title or "导出哪些设置"
        self.note = note or ("　勾上的才会写进文件。没勾的那一项，对方机器上原来\n"
                             "　的设置会原样留着 —— 不会被这台的样子覆盖掉。")
        # 勾选结果存到哪儿：导出是「记住上次那套」，远程是「写回本机配置」。
        self.persist = persist if persist is not None else save_shared_selection
        pal = app.cfg["palette"]
        self.pal = pal
        self.rows = []              # [(key, 那个方框 Label)]
        self._pt = None             # 拖标题栏时的按下点

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)
        self.body = tk.Frame(self.win, bg=pal["paper"])
        self.body.pack(fill="both", expand=True, padx=3, pady=3)

        self._build_header()
        for spec in self.specs:
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
        tk.Label(head, text="　" + self.title, bg=pal["ink"], fg=pal["paper"],
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

        tk.Label(self.body, text=self.note,
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

    def item_keys(self):
        """这张表里所有项的 key，按显示顺序。"""
        return [it["key"] for it in self.specs]

    def _pick_all(self):
        for key in self.item_keys():
            self.sel[key] = True
            self._paint(key)

    def _pick_none(self):
        for key in self.item_keys():
            self.sel[key] = False
            self._paint(key)

    def _confirm(self):
        picked = [k for k in self.item_keys() if self.sel.get(k)]
        if not picked:
            # 一项不带不等于「什么都不改」，它会让对方以为同步成功了 —— 更糟
            messagebox.showwarning(
                "还没挑东西",
                "至少勾一项。\n\n"
                "一项都不带的话，这份设置发出去什么也不会改，"
                "而对方会显示「成功」—— 反而更难发现问题。")
            return
        self.persist(self.sel)
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
    MIN_W = 700             # 缩放下限。取 700 不是随手定的：两列各 329 时，
                            # 最长的那行「自动检查新版本（每七天一次，静默不打扰）」
                            # 正好一行放得下；再窄就要折行，括号会孤零零掉到第二行。
    MIN_H = 320             # 缩放下限
    HEADER_H = 38           # 标题栏高（_build_header 里写死的高度，这里跟着）
    FOOTER_H = 76           # 页脚那块（分隔线 + 按钮行 + 上下留白）的估值

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

        # 面板尺寸（宽, 高）。0 = 没记过，按内容 + 屏幕自动算。
        pn = app.cfg.get("panel") or {}
        try:
            self.panel_w = int(pn.get("w") or 0)
            self.panel_h = int(pn.get("h") or 0)
        except (TypeError, ValueError):
            self.panel_w = self.panel_h = 0
        self._wraps = []        # [(Label, 这一行左右占掉的固定留白)] —— 缩窄时按列宽折行
        self._sbar_on = False   # 细滚动条现在露着没有
        self._resz0 = None      # 正在拖右下角时记下的起点
        self._resized = False   # 用户亲手调过尺寸没有（没调过就不必记住）

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)
        # 先在幕后把整棵树搭起来、量好尺寸，最后一次性露面。
        # 不 withdraw 的话，中途几次 update_idletasks 会让它在屏幕上
        # 一会儿大一会儿小地闪。withdraw 期间 Tk 照样算布局，reqheight 照样准。
        self.win.withdraw()

        self.body = tk.Frame(self.win, bg=pal["paper"])
        self.body.pack(fill="both", expand=True, padx=3, pady=3)

        self._build_header()
        self._build_columns()
        self._build_footer()
        self._build_resizer()
        self._fit_height()

        self.win.bind("<Escape>", lambda e: self.close())
        # 无边框窗口没有系统滚动条，滚轮得自己接（见 _on_wheel）
        self.win.bind_all("<MouseWheel>", self._on_wheel)
        self.win.deiconify()
        self.win.lift()
        try:
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        except tk.TclError:
            pass
        self._sync_scrollbar()
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
        # 中段 = 左边画布 + 右边一条自绘细滚动条。
        # 必须先 pack 滚动条（side="right"）、再 pack 画布：反过来的话画布
        # 先 fill=both 铺满整块，滚动条一格都分不到。
        self.mid = tk.Frame(self.body, bg=pal["paper"])
        self.mid.pack(fill="both", expand=True)
        # 轨道宽度**常驻** 8 像素（底色与纸色相同，用不着时看不出来），
        # 只让滑块现身或消失。切宽度或 pack/pack_forget 都会让画布跟着忽宽忽窄，
        # 内容在临界点上会来回抖一下 —— 常驻最稳。
        self.sbar = tk.Frame(self.mid, bg=pal["paper"], width=8)
        self.sbar.pack(side="right", fill="y")
        self.sbar.pack_propagate(False)
        self.thumb = tk.Frame(self.sbar, bg=pal["border_soft"], width=5)
        self.thumb.place(x=2, y=0, width=5, height=40)
        for part in (self.sbar, self.thumb):
            part.bind("<Button-1>", self._sbar_press)
            part.bind("<B1-Motion>", self._sbar_drag)
        self.canvas = tk.Canvas(self.mid, bg=pal["paper"], highlightthickness=0)
        self.canvas.pack(side="left", fill="both", expand=True)
        inner = tk.Frame(self.canvas, bg=pal["paper"])
        self._inner_win = self.canvas.create_window((0, 0), window=inner,
                                                    anchor="nw")
        inner.bind("<Configure>", self._on_inner_resize)
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
        self._build_shutdown(self.col_l)
        self._build_thresholds(self.col_l)
        self._build_shared(self.col_l)
        self._build_remote(self.col_l)
        self._build_window(self.col_r)
        self._build_notify(self.col_r)
        self._build_watch(self.col_r)

    def _on_inner_resize(self, _event=None):
        """内容高度变了（折行重排、加了一条规则……）就刷新滚动范围与滑块。"""
        try:
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
            self._sync_scrollbar()
        except tk.TclError:
            pass

    def _on_canvas_resize(self, event):
        try:
            self.canvas.itemconfigure(self._inner_win, width=event.width)
            # 顺手把滚动范围刷一遍：inner 的尺寸未必变（比如只是 canvas 变矮了），
            # 光靠 inner 的 <Configure> 会漏掉这种情况，于是滚轮「完全没反应」。
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
            # 列宽变了，长句子要重新算折行点 —— 不重算的话面板一缩窄，
            # 那几行说明就会被右边裁掉半句（它们是单行 Label，不会自己换行）。
            self._sync_wraps()
            self._sync_scrollbar()
        except tk.TclError:
            pass

    # ---- 尺寸：默认值 / 拖拽缩放 / 记忆 ----

    def _limits(self):
        """
        (最小宽, 最大宽, 最小高, 最大高)。

        上限留出任务栏与一点边距。下限也要跟着屏幕缩 —— 小屏机器上
        如果死守 700，面板会比屏幕还宽，反而拖不出屏幕外。
        """
        sw = self.win.winfo_screenwidth()
        sh = self.win.winfo_screenheight()
        wmin = min(SettingsPanel.MIN_W, max(360, sw - 60))
        hmin = min(SettingsPanel.MIN_H, max(200, sh - 120))
        return (wmin, max(wmin, sw - 100), hmin, max(hmin, sh - 90))

    def _fit_height(self):
        """
        定下打开面板时的尺寸。

        以前这里是「宽度跟随内容、高度 = 屏幕高 - 150」，在 2560×1440 上
        量出来是 1042×1307 —— 高度吃掉屏幕 91%，宽度还比两列真需要的多出
        一百多像素（内容被 canvas 的旧宽度反过来撑大了）。
        现在两条都改掉：宽度就按目标宽度走，过宽的句子改成折行去适配；
        高度优先用用户上次自己调好的尺寸，没调过才按内容算，而且**主动停在
        屏幕七成**——面板是来看设置的，不是来占屏的。
        """
        self.win.update_idletasks()
        if self.panel_w and self.panel_h:
            self._apply_panel_size(self.panel_w, self.panel_h)
            return
        self._auto_size()

    def _auto_size(self):
        """没记过尺寸时的默认大小：先定宽（让内容按真宽度重排），再量高度。"""
        _wmin, wmax, hmin, hmax = self._limits()
        w = min(self.W, wmax)
        self._apply_panel_size(w, hmin)      # 先按目标宽度布一次局
        self.win.update_idletasks()
        req_h = self.inner.winfo_reqheight()
        room = int(self.win.winfo_screenheight() * 0.70)
        h = min(req_h + SettingsPanel.HEADER_H + SettingsPanel.FOOTER_H + 6,
                max(hmin, room), hmax)
        self._apply_panel_size(w, h)

    def _apply_panel_size(self, w, h, keep_pos=False):
        """把尺寸落到窗口上（宽高都卡在「别顶出屏、别挤成一团」之间）。"""
        wmin, wmax, hmin, hmax = self._limits()
        self.panel_w = int(max(wmin, min(int(w), wmax)))
        self.panel_h = int(max(hmin, min(int(h), hmax)))
        if keep_pos:
            x, y = self.win.winfo_x(), self.win.winfo_y()
        else:
            sw = self.win.winfo_screenwidth()
            sh = self.win.winfo_screenheight()
            x = max(0, (sw - self.panel_w) // 2)
            # 居中但别顶到屏幕边：底部按钮被任务栏压住就点不到了
            y = max(6, min((sh - self.panel_h) // 2 - 40, sh - self.panel_h - 16))
        set_geometry(self.win, self.panel_w, self.panel_h, x, y)
        self.win.update_idletasks()
        try:
            self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        except tk.TclError:
            pass
        self._sync_wraps()
        self._sync_scrollbar()

    def _remember_panel_size(self):
        """
        把尺寸记进配置，下次打开还是这么大。

        刻意**不**在拖完的那一刻就写盘：面板里的设置要用户点「保存」才作数，
        拖个大小顺手把别的改动一起落盘，会变成「我没保存怎么生效了」。
        攒到关面板时写，就没有这个问题。
        """
        try:
            self.app.cfg["panel"] = {"w": int(self.panel_w), "h": int(self.panel_h)}
            save_config(self.app.cfg)
        except Exception as e:
            log_problem("remember_panel_size", e)

    def _reset_panel_size(self):
        """标题栏那颗角标：把面板恢复成「按内容和屏幕自动算」的大小。"""
        self.panel_w = self.panel_h = 0
        self._resized = False     # 回到自动之后，下次也该按内容算，不再固守旧尺寸
        self._auto_size()
        try:
            self.msg.configure(text="面板大小已复位", fg=self.pal["ink_soft"])
        except tk.TclError:
            pass

    def _build_resizer(self):
        """
        右下角那个能拖着改大小的角。

        无边框窗口（overrideredirect）连边框线都没有，自然也没有系统给的
        缩放热区 —— 不自己画一个，这扇窗就永远是死尺寸，用户的原话是
        「不能缩小与放大」。位置贴在右下角、离页脚按钮还有 30 多像素，
        不会挡住「保 存」。
        """
        pal = self.pal
        self.grip = tk.Label(self.win, text="◢", bg=pal["paper"], fg=pal["border"],
                             font=("Segoe UI", 9), cursor="size_nw_se",
                             padx=1, pady=0)
        self.grip.place(relx=1.0, rely=1.0, anchor="se", x=-4, y=-2)
        self.grip.bind("<Button-1>", self._resize_start)
        self.grip.bind("<B1-Motion>", self._resize_move)
        self.grip.bind("<ButtonRelease-1>", self._resize_done)
        self.grip.bind("<Enter>", lambda e: self.grip.configure(fg=pal["seal"]))
        self.grip.bind("<Leave>", lambda e: self.grip.configure(fg=pal["border"]))

    def _resize_start(self, event):
        self._resz0 = (event.x_root, event.y_root, self.panel_w, self.panel_h)

    def _resize_move(self, event):
        if not self._resz0:
            return
        x0, y0, w0, h0 = self._resz0
        # 拖右下角 = 左上角不动，只改宽高
        self._apply_panel_size(w0 + (event.x_root - x0),
                               h0 + (event.y_root - y0), keep_pos=True)

    def _resize_done(self, _event=None):
        self._resz0 = None
        self._resized = True
        self._remember_panel_size()

    # ---- 长句子折行 / 细滚动条 ----

    def _wrap(self, label, pad=36):
        """
        登记一个「面板窄了就折行」的长句子。pad = 这一行左右占掉的固定留白。

        面板能拖小之后，这些单行说明不重算折行点就会被右边裁掉半句 ——
        Tk 的 Label 默认不换行，界面上不会报错，只是字没了。
        """
        self._wraps.append((label, pad))
        try:
            label.configure(wraplength=max(140, int(self._col_w() - pad)))
        except tk.TclError:
            pass
        return label

    def _col_w(self):
        """一列现在的宽度。还没真正布局时（宽=1）按目标宽度估。"""
        try:
            cw = self.canvas.winfo_width()
        except tk.TclError:
            cw = 0
        if cw <= 1:
            cw = max(SettingsPanel.MIN_W, self.panel_w or self.W) - 6
        return max(120.0, (cw - 28) / 2.0)      # 28 = 两列各自的外留白

    def _sync_wraps(self):
        col = self._col_w()
        for label, pad in self._wraps:
            try:
                label.configure(wraplength=max(140, int(col - pad)))
            except tk.TclError:
                pass

    def _sync_scrollbar(self):
        """
        内容比可视区高时才让那条细滚动条现身，并按滚动位置摆好滑块。

        为什么非得有它：面板能拖小之后，底下被挡住的设置**一点提示都没有** ——
        用户想不到去滚鼠标，只会以为「我某一项设置不见了」。
        """
        try:
            if not self.canvas.winfo_exists():
                return
            box = self.canvas.bbox("all")
            view = self.canvas.winfo_height()
            total = max(int(box[3]) if box else 0, 1)
        except (tk.TclError, TypeError, IndexError):
            return
        need = total > view + 6
        if need != self._sbar_on:
            if need:
                self.thumb.place(x=2, y=0, width=5, height=40)
            else:
                self.thumb.place_forget()
            self._sbar_on = need
        if not need:
            return
        try:
            track = self.sbar.winfo_height()
            if track <= 1:
                return
            th = max(28, min(track, int(track * (view / float(total)))))
            top = int((track - th) * float(self.canvas.yview()[0] or 0))
            self.thumb.place(x=2, y=top, width=5, height=th)
        except tk.TclError:
            pass

    def _sbar_press(self, event):
        self._sbar_drag(event)

    def _sbar_drag(self, event):
        """把滑块拖到的位置换算成画布的滚动比例。"""
        try:
            track = self.sbar.winfo_height()
            th = self.thumb.winfo_height()
            if track - th <= 1:
                return
            y = event.y_root - self.sbar.winfo_rooty() - th / 2.0
            self.canvas.yview_moveto(min(1.0, max(0.0, y / float(track - th))))
            self._sync_scrollbar()
        except tk.TclError:
            pass

    def _on_wheel(self, event):
        """内容比面板高时，滚轮上下滚（比把整个窗口挪来挪去自然得多）。"""
        try:
            if not self.canvas.winfo_exists():
                return
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            self._sync_scrollbar()
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

        # 面板大小复位。用户把面板拖成一条细缝或者拖出屏幕外之后，
        # 得有个不用重装就能回去的入口 —— 右下角那个角是拖出来的，
        # 拖坏了也得有一键还原。
        fit = tk.Label(self.header, text="⤢", bg=pal["ink"], fg=pal["border_soft"],
                       font=("Segoe UI", 10), cursor="hand2", padx=11)
        fit.pack(side="right", fill="y")
        fit.bind("<Button-1>", lambda e: self._reset_panel_size())
        fit.bind("<Enter>", lambda e: fit.configure(bg=pal["border"], fg="#FFF8EC"))
        fit.bind("<Leave>", lambda e: fit.configure(bg=pal["ink"], fg=pal["border_soft"]))
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
                                font=(app.fam_cn, 10), anchor="w", justify="left")
        self._wrap(self.preview, 40)
        self.preview.pack(fill="x", padx=20, pady=(3, 0))

        # 提示压成两行：左列是整块面板最高的一列，这里多一行，
        # 「拖到最大能一眼看全」那条就守不住（内容高度是贴着上限走的）。
        self._wrap(tk.Label(parent, text="　格式：月.日.时.分　随便什么分隔都行，"
                                         "如 10.1.11.30",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(
            fill="x", padx=18, pady=(2, 0))
        self._wrap(tk.Label(parent, text="　　　0330＝03:30；年份写在最前面，"
                                         "如 2026.10.1",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(
            fill="x", padx=18)

        # 「＋30 天」一键顺延。跟右键菜单第一项是同一个按钮：没过期在原时刻
        # 上加，过期了从现在起算。点击立刻落盘生效，不用再点「保 存」——
        # 它改的就是配置本身，保存按钮那套校验是给手打的目标文本用的。
        plusrow = tk.Frame(parent, bg=pal["paper"])
        plusrow.pack(fill="x", padx=18, pady=(4, 0))
        plus = tk.Label(plusrow, text="＋30 天", bg=pal["paper"], fg=pal["seal"],
                        font=(app.fam_cn, 9, "bold"), cursor="hand2",
                        padx=8, pady=2)
        plus.pack(side="left")
        plus.bind("<Button-1>", lambda e: self._on_plus30())
        plus.bind("<Enter>", lambda e: plus.configure(bg=pal["border_soft"],
                                                      fg="#FFF8EC"))
        plus.bind("<Leave>", lambda e: plus.configure(bg=pal["paper"],
                                                      fg=pal["seal"]))
        self._wrap(tk.Label(plusrow,
                            text="过期的从现在起算，没过期的在原时刻上加；"
                                 "点了立即生效",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 34).pack(
            side="left", padx=(4, 0))
        self._preview()

    def _on_plus30(self):
        """面板上的「＋30 天」：改完把输入框与预览行同步成新时刻。"""
        err = self.app.extend_target_days(30)
        if err:
            self.preview.configure(text="✕　" + err, fg=self.pal["seal"])
            return
        self.refresh_target_entry()
        self.msg.configure(text="倒计时已 +30 天，立即生效（无需保存）")

    def refresh_target_entry(self):
        """
        把输入框刷成当前配置里的目标时刻。

        右键菜单那边也能 +30 天（面板开着时同样会走到这里）——
        两处谁改了，框里都得跟上，否则用户再点「保 存」会把刚顺延的
        时刻拿旧文本改回去，那比不加按钮还糟。
        """
        self.entry.delete(0, "end")
        self.entry.insert(0, self.app.cfg.get("target", ""))
        self._preview()

    # ---- 定时关机 ----

    def _build_shutdown(self, parent):
        """
        定时关机：网址取日期（或设置文件里写死时刻）→ 那就是**关机时刻**
        → 到点关机。

        三点是刻意这么写的：

        · 取回的时刻**只用来关机**，不动上面那个「目标时刻」。那是用户自己设的
          倒计时，跟「这台机器几点关」是两件事。早先的版本把两者合成一个，
          取一次日期就把用户的倒计时换掉了 —— 已经被指出来过一次，别再合并。
        · 不给「关机时刻」单独放输入框：那个时刻的权威来源是网址或设置文件，
          再给一个框两处都能改，用户永远搞不清以哪个为准。想知道现在定的是几点，
          看下面那行「当前关机时刻」。
        · 设置文件里写着关机时刻时，下面会多一行灰字说明它的来处 ——
          用户没填网址却看见关机时刻，不至于以为程序出了错。
        """
        app, pal = self.app, self.pal
        sd = app.shutdown_cfg()

        head = self._section("定时关机", parent)
        tk.Label(head, text="两个时刻谁先到，就按谁关",
                 bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="right")

        wrap = tk.Frame(parent, bg=pal["paper"])
        wrap.pack(fill="x", padx=18)

        self.var_shut = tk.BooleanVar(value=bool(sd.get("enabled")))
        self._wrap(tk.Checkbutton(wrap, text="  到点就把电脑关掉（关机前会弹窗问一句）",
                                  variable=self.var_shut, bg=pal["paper"],
                                  fg=pal["ink"], selectcolor="#FFFBF2",
                                  activebackground=pal["paper"],
                                  activeforeground=pal["seal"],
                                  font=(app.fam_cn, 10), anchor="w",
                                  justify="left", bd=0,
                                  highlightthickness=0), 56).pack(fill="x")

        # 第二个来源。默认勾上：用户明确要「倒计时到了也关」。
        # 不勾就是只听网址的 —— 那种机器上倒计时只是个提醒日。
        self.var_from_target = tk.BooleanVar(value=bool(sd.get("from_target", True)))
        self._wrap(tk.Checkbutton(wrap, text="  倒计时目标到了也关（不勾＝只听网址的）",
                                  variable=self.var_from_target, bg=pal["paper"],
                                  fg=pal["ink"], selectcolor="#FFFBF2",
                                  activebackground=pal["paper"],
                                  activeforeground=pal["seal"],
                                  font=(app.fam_cn, 10), anchor="w",
                                  justify="left", bd=0,
                                  highlightthickness=0), 56).pack(fill="x")

        row = tk.Frame(wrap, bg=pal["paper"])
        row.pack(fill="x", pady=(6, 0))
        tk.Label(row, text="网址", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=7, anchor="w").pack(side="left")
        self.entry_url = tk.Entry(row, font=(app.fam_num, 10), bg="#FFFBF2",
                                  fg=pal["ink"], relief="flat",
                                  insertbackground=pal["seal"],
                                  highlightthickness=1,
                                  highlightbackground=pal["border_soft"],
                                  highlightcolor=pal["seal"])
        self.entry_url.insert(0, sd.get("url") or "")
        self.entry_url.pack(side="left", fill="x", expand=True, ipady=3)
        fetch_btn = tk.Label(row, text="获取", bg=pal["paper"], fg=pal["ink_soft"],
                             font=(app.fam_cn, 10), cursor="hand2",
                             padx=8, pady=2, relief="solid", bd=1)
        fetch_btn.pack(side="left", padx=(8, 0))
        fetch_btn.bind("<Button-1>", lambda e: self._fetch_site_now())
        fetch_btn.bind("<Enter>", lambda e: fetch_btn.configure(fg=pal["seal"]))
        fetch_btn.bind("<Leave>", lambda e: fetch_btn.configure(fg=pal["ink_soft"]))

        self.site_msg = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                            fg=pal["ink_soft"], font=(app.fam_cn, 9),
                                            anchor="w", justify="left"), 40)
        self.site_msg.pack(fill="x", pady=(4, 0))
        self._show_site_result()

        opt = tk.Frame(wrap, bg=pal["paper"])
        opt.pack(fill="x", pady=(6, 0))
        self.var_auto_site = tk.BooleanVar(value=bool(sd.get("auto_fetch", True)))
        tk.Checkbutton(opt, text="  启动时自动取一次", variable=self.var_auto_site,
                       bg=pal["paper"], fg=pal["ink"], selectcolor="#FFFBF2",
                       activebackground=pal["paper"], activeforeground=pal["seal"],
                       font=(app.fam_cn, 10), anchor="w", bd=0,
                       highlightthickness=0).pack(side="left")

        # 「每隔 N 小时再取一次」单独占一行。原来它跟上面那句挤在同一行，
        # 面板一缩窄，右边「小时再取一次」几个字就被裁掉了 —— 单行控件
        # 不会自己换行，界面也不报错，就是字没了。
        opt2 = tk.Frame(wrap, bg=pal["paper"])
        opt2.pack(fill="x", pady=(2, 0))
        self.var_site_hours = tk.BooleanVar(
            value=float(sd.get("refresh_hours") or 0) > 0)
        tk.Checkbutton(opt2, text="  每隔", variable=self.var_site_hours,
                       bg=pal["paper"], fg=pal["ink"], selectcolor="#FFFBF2",
                       activebackground=pal["paper"], activeforeground=pal["seal"],
                       font=(app.fam_cn, 10), bd=0,
                       highlightthickness=0).pack(side="left")
        self.var_hours = tk.StringVar(
            value="%g" % float(sd.get("refresh_hours") or 6))
        tk.Entry(opt2, textvariable=self.var_hours, width=4, justify="center",
                 font=(app.fam_num, 10), bg="#FFFBF2", fg=pal["ink"],
                 relief="flat", insertbackground=pal["seal"],
                 highlightthickness=1, highlightbackground=pal["border_soft"],
                 highlightcolor=pal["seal"]).pack(side="left", padx=(2, 2), ipady=2)
        tk.Label(opt2, text="小时再取一次", bg=pal["paper"], fg=pal["ink"],
                 font=(app.fam_cn, 10)).pack(side="left")

        row2 = tk.Frame(wrap, bg=pal["paper"])
        row2.pack(fill="x", pady=(6, 0))
        tk.Label(row2, text="关机前弹窗等", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10)).pack(side="left")
        self.var_grace = tk.StringVar(
            value="%d" % int(sd.get("grace_sec", SHUTDOWN_GRACE_DEFAULT)))
        tk.Entry(row2, textvariable=self.var_grace, width=5, justify="center",
                 font=(app.fam_num, 10, "bold"), bg="#FFFBF2", fg=pal["ink"],
                 relief="flat", insertbackground=pal["seal"],
                 highlightthickness=1, highlightbackground=pal["border_soft"],
                 highlightcolor=pal["seal"]).pack(side="left", padx=(4, 4), ipady=3)
        tk.Label(row2, text="秒（没人理就关）", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10)).pack(side="left")

        # 现在定的是几点关 —— 单独一行、加粗，取完日期当场能看见。
        # 没有这一行的话，用户点完「获取」只能从一行小字里猜到底取到了什么。
        self.shut_at_lbl = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                               fg=pal["seal"],
                                               font=(app.fam_cn, 10, "bold"),
                                               anchor="w", justify="left"), 40)
        self.shut_at_lbl.pack(fill="x", pady=(8, 0))

        # 关机时刻写在设置文件里时的那一行说明。只读 —— 那个时刻的权威是
        # 远程设置 / 共用设置那份文件（和网址同一个道理：再给一个输入框，
        # 两处都能改，用户永远搞不清以哪个为准）。要改去改那份配置文件。
        # **刻意不在这里 pack**：没指定 at 时它一行都不占（面板内容高度是
        # 卡着屏幕七成算的，多一行空Label就可能把滚动条顶出来）。
        # 露不露面由 _sync_shutdown_note 按 cfg.shutdown.at 决定。
        self.shut_src_lbl = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                                fg=pal["ink_soft"],
                                                font=(app.fam_cn, 9),
                                                anchor="w", justify="left"), 40)

        self.shut_msg = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                            fg=pal["ink_soft"], font=(app.fam_cn, 9),
                                            anchor="w", justify="left"), 40)
        self.shut_msg.pack(fill="x", pady=(4, 0))

        # 演练入口。「要等很久才可能发生」的功能都得有「现在就看」——
        # 否则用户点完保存，屏幕上什么都不会发生，等于没法验证。
        try_btn = tk.Label(wrap, text="　试一遍（弹窗但不真关机）",
                           bg=pal["paper"], fg=pal["ink_soft"],
                           font=(app.fam_cn, 10), cursor="hand2", anchor="w")
        try_btn.pack(fill="x", pady=(6, 0))
        try_btn.bind("<Button-1>", lambda e: self._shutdown_drill())
        try_btn.bind("<Enter>", lambda e: try_btn.configure(fg=pal["seal"]))
        try_btn.bind("<Leave>", lambda e: try_btn.configure(fg=pal["ink_soft"]))

        self._wrap(tk.Label(wrap, text="　网址那个时刻只用来关机，不会动上面那个倒计时目标；"
                                        "倒计时那个也一样，只用来关机。两个谁先到就按谁关。",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(fill="x", pady=(2, 0))

        self._sync_shutdown_note()

    def _shutdown_drill(self):
        """面板上点「试一遍」：真弹那扇窗，但走到头也不会关机。"""
        if not hasattr(self, "shut_msg"):
            return
        why = self.app.shutdown_drill()
        if why:
            self.shut_msg.configure(text="　" + why, fg=self.pal["seal"])
        else:
            self.shut_msg.configure(
                text="　弹出来了 —— 倒计时走完的话，真关机就是这个样子。",
                fg=self.pal["ink_soft"])

    def _show_site_result(self):
        """把最近一次取日期的结果写在面板上，免得只能靠猜。"""
        if not hasattr(self, "site_msg"):
            return
        info = self.app.site_date or {}
        if not info.get("at"):
            self.site_msg.configure(text="　还没取过。点右边「获取」试一次。",
                                    fg=self.pal["border"])
            return
        text = "　%s　%s" % (info.get("at", "")[:16], info.get("note") or "")
        self.site_msg.configure(text=text,
                                fg="#4F7A52" if info.get("ok") else self.pal["seal"])

    def _sync_shutdown_note(self):
        """
        面板上要能一眼看见：现在会按几点关、正在推进到哪一步、有没有错过。

        第一行显示的是**两个来源里先到的那个** —— 那才是真正会触发关机
        的时刻。只显示网址那个的话，用户设了更早的倒计时会看不懂
        「为什么明明还没到点就关了」。
        """
        if not hasattr(self, "shut_msg"):
            return
        # 第一行只算「此刻」—— 面板里另有一个每秒跑的轮询会再刷一次，
        # 所以「还有几小时几分」是活的（见 _poll_watch）。
        if hasattr(self, "shut_at_lbl"):
            # 有排上的就用印泥色（醒目），「还没有 / 已处理过」用淡色（不抢眼）。
            dt, _src = self.app.shutdown_next()
            self.shut_at_lbl.configure(
                text="　当前关机时刻：%s" % self.app.shutdown_left_text(),
                fg=self.pal["seal"] if dt is not None else self.pal["ink_soft"])
        # 关机时刻是设置文件里写死的时候，说清它从哪儿来 ——
        # 否则用户没填网址却看见一个关机时刻，只会以为程序出了错。
        # 没指定 at 时这行整个不占地方（pack_forget），面板高度不受影响。
        if hasattr(self, "shut_src_lbl"):
            at_text = ((self.app.cfg.get("shutdown") or {}).get("at") or "").strip()
            if at_text:
                self.shut_src_lbl.configure(
                    text="　（这个时刻写在设置文件里，要改去改那份配置文件）")
                if not self.shut_src_lbl.winfo_manager():
                    # before= 钉住位置：它在「当前关机时刻」与「关机状态」之间。
                    # 不钉的话 pack 会把它甩到这一节末尾（试一遍按钮后面）去。
                    self.shut_src_lbl.pack(fill="x", pady=(2, 0),
                                           before=self.shut_msg)
            elif self.shut_src_lbl.winfo_manager():
                self.shut_src_lbl.pack_forget()
        st = self.app.shutdown_state or {}
        phase = st.get("phase") or ""
        if phase == "asking":
            self.shut_msg.configure(
                text="　关机确认窗开着，等你表态（关掉窗 / 按 Esc 都算「照关」）。"
                     "要彻底停下：右键小窗口 →「取消定时关机」。",
                fg=self.pal["seal"])
        elif phase == "retrying":
            self.shut_msg.configure(
                text="　已发出关机命令（第 %s 次），一分钟后还关不掉就再试一次。"
                     "要停下：右键小窗口 →「取消定时关机」。"
                     % (st.get("tries") or 1), fg=self.pal["seal"])
        elif st.get("missed_at"):
            self.shut_msg.configure(text="　" + (st.get("note") or ""),
                                    fg=self.pal["ink_soft"])
        elif st.get("cancelled_at"):
            self.shut_msg.configure(text="　" + (st.get("note") or ""),
                                    fg=self.pal["ink_soft"])
        else:
            self.shut_msg.configure(text="", fg=self.pal["ink_soft"])

    def _fetch_site_now(self):
        """面板上点「获取」：拿输入框里现打的网址去取（不必先保存）。"""
        url = self.entry_url.get().strip()
        if not url:
            self.site_msg.configure(text="　先填网址", fg=self.pal["seal"])
            return
        err = self.app.fetch_site_now(manual=True, url=url, done=self._site_done)
        if err:
            self.site_msg.configure(text="　" + err, fg=self.pal["seal"])
        else:
            self.site_msg.configure(text="　正在取…", fg=self.pal["ink_soft"])

    def _site_done(self, dt, err):
        """取回来了。回调跑在主线程，但仍然要防面板已经关了。"""
        try:
            if not self.win.winfo_exists():
                return
        except tk.TclError:
            return
        if err or dt is None:
            self.site_msg.configure(text="　" + (err or "没取到"), fg=self.pal["seal"])
            self._sync_shutdown_note()
            return
        # 刻意**不动**上面那个目标框：取回来的时刻只作关机用。
        # 早先这里会把取到的时刻填进目标框连配置一起改，用户设的倒计时
        # 就这么被换掉了 —— 那是错的，别再退回去。
        self.site_msg.configure(
            text="　取到了：%s（已设为关机时刻，倒计时目标没动）" % pretty_target(dt),
            fg="#4F7A52")
        self._sync_shutdown_note()

    def _collect_shutdown(self):
        raw = self.var_grace.get().strip()
        try:
            grace = int(float(raw or SHUTDOWN_GRACE_DEFAULT))
        except ValueError:
            return None, "「关机前弹窗等几秒」要填数字（0 ~ %d）" % SHUTDOWN_GRACE_MAX
        if not 0 <= grace <= SHUTDOWN_GRACE_MAX:
            return None, "「关机前弹窗等几秒」要在 0 ~ %d 之间" % SHUTDOWN_GRACE_MAX

        hours = 0.0
        if self.var_site_hours.get():
            try:
                hours = float(self.var_hours.get().strip() or 0)
            except ValueError:
                return None, "「每隔几小时再取一次」要填数字，可以带小数"
            if not 0 < hours <= 168:
                return None, "「每隔几小时再取一次」要在 0 ~ 168 之间（一周）"

        url = self.entry_url.get().strip()
        if url and not re.match(r"^https?://", url, re.I):
            # 用户十有八九只写域名。这里替他补上并回显 ——
            # 悄悄补而不显示的话，他下次看到自己写的那行会以为程序没记住。
            url = "http://" + url
            self.entry_url.delete(0, "end")
            self.entry_url.insert(0, url)

        # 从当前配置起手再改面板上能编辑的那几项 —— 和 _collect_remote 同一套路子。
        # 关键是 **at 原样带回**：关机时刻的权威是设置文件（或网址），面板上
        # 没有它的输入框（两处都能改，用户永远搞不清以哪个为准），保存时绝不能
        # 把它冲掉。deep_merge 本来也保得住，这里显式写出来是为了别被将来
        # 改合并逻辑的人悄悄弄丢。
        cfg = dict(self.app.shutdown_cfg())
        cfg.update({
            "enabled": bool(self.var_shut.get()),
            "from_target": bool(self.var_from_target.get()),
            "url": url,
            "auto_fetch": bool(self.var_auto_site.get()),
            "refresh_hours": hours,
            "grace_sec": grace,
        })
        return cfg, None

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

    def _build_remote(self, parent):
        """
        「远程设置」一节：从一个网址把设置取回来。

        和上面「多机共用设置」是同一件事的两种走法 —— 那个靠 U 盘拷文件，
        这个让每台机器自己去网址取。两节紧挨着放不是巧合：
        同一个格式、同一套校验、同一套勾选项，只是搬运方式不同。
        """
        app, pal = self.app, self.pal
        rc = app.remote_cfg()
        sec = app.secret or {}

        head = self._section("远程设置", parent)
        tk.Label(head, text="从网址取回", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="right")

        wrap = tk.Frame(parent, bg=pal["paper"])
        wrap.pack(fill="x", padx=18)

        self.var_remote = tk.BooleanVar(value=bool(rc.get("enabled")))
        self._wrap(tk.Checkbutton(wrap, text="  自动从网址取回设置",
                                  variable=self.var_remote, bg=pal["paper"],
                                  fg=pal["ink"], selectcolor="#FFFBF2",
                                  activebackground=pal["paper"],
                                  activeforeground=pal["seal"],
                                  font=(app.fam_cn, 10), anchor="w",
                                  justify="left", bd=0,
                                  highlightthickness=0), 56).pack(fill="x")

        self.entry_rurl = self._remote_entry(wrap, "网址", rc.get("url"))

        row = tk.Frame(wrap, bg=pal["paper"])
        row.pack(fill="x", pady=(6, 0))
        tk.Label(row, text="认证", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=5, anchor="w").pack(side="left")
        self.var_rauth = tk.StringVar(value=remote_auth_label(rc.get("auth")))
        menu = tk.OptionMenu(row, self.var_rauth,
                             *[lbl for lbl, _ in REMOTE_AUTH_LABELS])
        menu.configure(bg="#FFFBF2", fg=pal["ink"], font=(app.fam_cn, 10),
                       relief="solid", bd=1, highlightthickness=0,
                       activebackground=pal["paper"],
                       activeforeground=pal["seal"], anchor="w", width=12)
        menu["menu"].configure(bg="#FFFBF2", fg=pal["ink"],
                               font=(app.fam_cn, 10))
        menu.pack(side="left", padx=(8, 0))

        self.entry_ruser = self._remote_entry(wrap, "用户名", rc.get("user"))
        self.entry_rpass = self._remote_entry(wrap, "密码",
                                              sec.get("remote_password"), show="●")
        self.entry_rtoken = self._remote_entry(wrap, "令牌",
                                               sec.get("remote_token"), show="●")
        self.entry_rhname = self._remote_entry(wrap, "头名称",
                                               sec.get("remote_header_name"))
        self.entry_rhval = self._remote_entry(wrap, "头内容",
                                              sec.get("remote_header_value"), show="●")

        self._wrap(tk.Label(wrap, text="　按上面选的认证方式填，用不到的那几行留空就行。",
                            bg=pal["paper"], fg=pal["border"],
                            font=(app.fam_cn, 9), anchor="w", justify="left"), 40).pack(
            fill="x", pady=(3, 0))
        self._wrap(tk.Label(wrap, text="　密码只存本机（已加密），不会写进远端那份设置里。",
                            bg=pal["paper"], fg=pal["border"],
                            font=(app.fam_cn, 9), anchor="w", justify="left"), 40).pack(
            fill="x", pady=(1, 0))

        bar = tk.Frame(wrap, bg=pal["paper"])
        bar.pack(fill="x", pady=(8, 0))
        for text, act in (("现在就拉一次", self._pull_remote_now),
                          ("挑同步哪些项…", self._pick_remote_items)):
            btn = tk.Label(bar, text=text, bg=pal["paper"], fg=pal["ink_soft"],
                           font=(app.fam_cn, 10), cursor="hand2", padx=10, pady=4,
                           relief="solid", bd=1)
            btn.pack(side="left", padx=(0, 10))
            btn.bind("<Button-1>", lambda e, f=act: f())
            btn.bind("<Enter>", lambda e, b=btn: b.configure(fg=pal["seal"]))
            btn.bind("<Leave>", lambda e, b=btn: b.configure(fg=pal["ink_soft"]))

        self.remote_msg = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                              fg=pal["ink_soft"], font=(app.fam_cn, 9),
                                              anchor="w", justify="left"), 40)
        self.remote_msg.pack(fill="x", pady=(4, 0))
        self._sync_remote_note()

    def _remote_entry(self, parent, label, value, show=None):
        """远程设置里的一行输入框。五行长得一样，抽出来省得抄五遍。"""
        app, pal = self.app, self.pal
        row = tk.Frame(parent, bg=pal["paper"])
        row.pack(fill="x", pady=(6, 0))
        tk.Label(row, text=label, bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=5, anchor="w").pack(side="left")
        entry = tk.Entry(row, bg="#FFFBF2", fg=pal["ink"], relief="solid", bd=1,
                         font=(app.fam_cn, 10), highlightthickness=0,
                         insertbackground=pal["ink"], show=show or "")
        entry.insert(0, value or "")
        entry.pack(side="left", fill="x", expand=True, padx=(8, 0), ipady=2)
        return entry

    def _sync_remote_note(self):
        """把「上次拉成没成」写在按钮下面 —— 让用户不用猜。"""
        if not hasattr(self, "remote_msg"):
            return
        self.remote_msg.configure(text="　" + self.app.remote_status_text(),
                                  fg=self.pal["ink_soft"])

    def _collect_remote(self):
        """把远程设置这一段收出来。返回 (配置, 凭据, 错误)。"""
        mode = remote_auth_key(self.var_rauth.get())
        url = self.entry_rurl.get().strip()
        enabled = bool(self.var_remote.get())
        if enabled and not url:
            return None, None, "勾了「自动从网址取回设置」，请先填写网址"
        if enabled and mode == "basic" and not self.entry_ruser.get().strip():
            return None, None, "认证方式选了「用户名 + 密码」，用户名不能空着"
        cfg = dict(self.app.remote_cfg())
        cfg.update({"enabled": enabled, "url": url, "auth": mode,
                    "user": self.entry_ruser.get().strip()})
        creds = {"remote_password": self.entry_rpass.get(),
                 "remote_token": self.entry_rtoken.get().strip(),
                 "remote_header_name": self.entry_rhname.get().strip(),
                 "remote_header_value": self.entry_rhval.get()}
        return cfg, creds, None

    def _pull_remote_now(self):
        """
        「现在就拉一次」：先用面板上刚填的值试一回。

        刻意**不先保存** —— 用户可能只是改了个网址想试试通不通，
        通了他才保存。试一下就顺手把设置存了，反而让人不敢点。
        """
        cfg, creds, err = self._collect_remote()
        if err:
            self.remote_msg.configure(text="　" + err, fg=self.pal["seal"])
            return
        self.remote_msg.configure(text="　正在取…", fg=self.pal["ink_soft"])

        def done(ok, why):
            if ok:
                self.remote_msg.configure(
                    text="　取到了，已按远端那份更新（只改挑中的项）",
                    fg="#4F7A52")
            else:
                self.remote_msg.configure(
                    text="　没取到：" + (why or "原因不明"), fg=self.pal["seal"])

        why = self.app.fetch_remote_with(cfg, creds, done=done)
        if why:
            self.remote_msg.configure(text="　" + why, fg=self.pal["seal"])

    def _pick_remote_items(self):
        """挑「从网址取回来的那份，认哪几项」。复用导出共用设置那个小窗。"""
        self._picker = ExportPicker(
            self.app, self._remote_items_picked,
            specs=remote_item_specs(), current=self.app.remote_items(),
            title="同步哪些项",
            note="　勾上的才会从远端取回来；没勾的那项，本机保持原样。\n"
                 "　邮箱授权码不在这里 —— 密码只在本机填，永远不从网上取。",
            persist=self._save_remote_items)

    def _save_remote_items(self, selection):
        """挑完把结果记进配置（跟着「保存」一起落盘）。"""
        cfg = self.app.remote_cfg()
        cfg["items"] = dict((k, bool(v)) for k, v in selection.items())
        self.app.cfg["remote"] = cfg
        self._sync_remote_note()
        self.remote_msg.configure(text="　已挑好；点「保存」后长期生效。",
                                  fg=self.pal["ink_soft"])

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
                          (self.var_autoupd, "自动检查新版本（每七天一次，不打扰）")):
            self._wrap(tk.Checkbutton(parent, text="  " + text, variable=var,
                                      bg=pal["paper"], fg=pal["ink"],
                                      selectcolor="#FFFBF2",
                                      activebackground=pal["paper"],
                                      activeforeground=pal["seal"],
                                      font=(app.fam_cn, 10), anchor="w",
                                      justify="left", bd=0,
                                      highlightthickness=0), 62).pack(
                fill="x", padx=20)

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

        self._wrap(tk.Label(parent, text="　拖窗口边缘也能改；勾了「锁定窗口尺寸」就改不动。",
                            bg=pal["paper"], fg=pal["border"],
                            font=(app.fam_cn, 9), anchor="w", justify="left"), 40).pack(
            fill="x", padx=18, pady=(0, 6))

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
        self._wrap(tk.Checkbutton(wrap, text="  启用邮件提醒（关掉则只变色、不发信）",
                                  variable=self.var_notify, bg=pal["paper"],
                                  fg=pal["ink"], selectcolor="#FFFBF2",
                                  activebackground=pal["paper"],
                                  activeforeground=pal["seal"],
                                  font=(app.fam_cn, 10), anchor="w",
                                  justify="left", bd=0,
                                  highlightthickness=0), 56).pack(fill="x")

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

        self._wrap(tk.Label(wrap, text="　授权码非登录密码，要在邮箱里单独申请；"
                                       "收件邮箱留空即发给自己",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(fill="x", pady=(2, 0))
        self._wrap(tk.Label(wrap, text="　本机抬头用于分辨是哪台电脑寄的，会出现在发件人、"
                                       "主题前缀和正文落款三处；留空即不加。"
                                       "默认取计算机名「%s」" % machine_name(),
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(fill="x", pady=(1, 0))

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

    # ---- 窗口盯守 ----

    def _build_watch(self, parent):
        """
        窗口盯守：挑一扇窗，定期看一眼它还在不在，**连续不见满设定的分钟数**
        才寄信（那段时间里程序会反复核实，它一出现就自动撤销）。

        下拉框里放的是「此刻开着的窗口」，但真正存下来的是**关键字**。
        为什么不直接存整条标题：游戏标题里常带角色名、等级、在线人数，
        下次开起来就是另一条了。用户挑一次之后可以自己把那一段删短
        （比如只留游戏名），那才是稳的。
        """
        app, pal = self.app, self.pal
        wc = app.watch_cfg()

        head = self._section("窗口盯守", parent)
        tk.Label(head, text="连续不见才寄信", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9)).pack(side="right")

        wrap = tk.Frame(parent, bg=pal["paper"])
        wrap.pack(fill="x", padx=18)

        self.var_watch = tk.BooleanVar(value=bool(wc.get("enabled")))
        # 文案刻意短：「盯一扇窗…」比「盯着某扇窗…」少两个字 ——
        # 复选框是单行控件，长了会把整列撑宽（折行只是兜底）。
        self._wrap(tk.Checkbutton(wrap, text="  盯一扇窗，不见了就寄信（默认要寄）",
                                  variable=self.var_watch, bg=pal["paper"],
                                  fg=pal["ink"], selectcolor="#FFFBF2",
                                  activebackground=pal["paper"],
                                  activeforeground=pal["seal"],
                                  font=(app.fam_cn, 10), anchor="w",
                                  justify="left", bd=0,
                                  highlightthickness=0), 56).pack(fill="x")

        row = tk.Frame(wrap, bg=pal["paper"])
        row.pack(fill="x", pady=(6, 0))
        tk.Label(row, text="选窗口", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=7, anchor="w").pack(side="left")
        self.var_pick = tk.StringVar(value="（点这里挑一个）")
        self.win_pick = tk.OptionMenu(row, self.var_pick, "（点这里挑一个）")
        self.win_pick.configure(bg="#FFFBF2", fg=pal["ink"], activebackground="#FFFBF2",
                                font=(app.fam_cn, 10), highlightthickness=1, bd=0,
                                relief="flat", anchor="w",
                                highlightbackground=pal["border_soft"])
        self.win_pick["menu"].configure(font=(app.fam_cn, 10), bg="#FFFBF2",
                                        fg=pal["ink"], activebackground=pal["seal"],
                                        activeforeground="#FFF8EC")
        self.win_pick.pack(side="left", fill="x", expand=True)
        ref = tk.Label(row, text="刷新", bg=pal["paper"], fg=pal["ink_soft"],
                       font=(app.fam_cn, 10), cursor="hand2",
                       padx=8, pady=2, relief="solid", bd=1)
        ref.pack(side="left", padx=(8, 0))
        ref.bind("<Button-1>", lambda e: self._reload_window_list(True))
        ref.bind("<Enter>", lambda e: ref.configure(fg=pal["seal"]))
        ref.bind("<Leave>", lambda e: ref.configure(fg=pal["ink_soft"]))

        row2 = tk.Frame(wrap, bg=pal["paper"])
        row2.pack(fill="x", pady=(6, 0))
        tk.Label(row2, text="关键字", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10), width=7, anchor="w").pack(side="left")
        self.entry_watch = tk.Entry(row2, font=(app.fam_num, 10), bg="#FFFBF2",
                                    fg=pal["ink"], relief="flat",
                                    insertbackground=pal["seal"],
                                    highlightthickness=1,
                                    highlightbackground=pal["border_soft"],
                                    highlightcolor=pal["seal"])
        self.entry_watch.insert(0, wc.get("title") or "")
        self.entry_watch.pack(side="left", fill="x", expand=True, ipady=3)

        self._wrap(tk.Label(wrap, text="　标题里常带角色名、等级、在线人数，存整条下次就对不上了。"
                                       "挑好之后把关键字改短，只留认得出那扇窗的一段。",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(fill="x", pady=(2, 0))

        row3 = tk.Frame(wrap, bg=pal["paper"])
        row3.pack(fill="x", pady=(6, 0))
        tk.Label(row3, text="每隔", bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 10)).pack(side="left")
        self.var_interval = tk.StringVar(
            value="%g" % float(wc.get("interval_min") or 30))
        tk.Entry(row3, textvariable=self.var_interval, width=5, justify="center",
                 font=(app.fam_num, 10, "bold"), bg="#FFFBF2", fg=pal["ink"],
                 relief="flat", insertbackground=pal["seal"],
                 highlightthickness=1, highlightbackground=pal["border_soft"],
                 highlightcolor=pal["seal"]).pack(side="left", padx=(4, 4), ipady=3)
        # 这两行原本是整句横排的，右列因此被撑到 468 宽（面板宽也就跟着虚胖）。
        # 接进折行体系之后，面板缩窄时它们自己会断行 —— 不再是宽度的下限。
        self._wrap(tk.Label(row3, text="分钟看一眼；看见过之后，不见了就先问你一句：",
                            bg=pal["paper"], fg=pal["ink_soft"],
                            font=(app.fam_cn, 10), anchor="w", justify="left"), 118).pack(
            side="left")

        row4 = tk.Frame(wrap, bg=pal["paper"])
        row4.pack(fill="x", pady=(4, 0))
        tk.Label(row4, text="　等", bg=pal["paper"], fg=pal["ink"],
                 font=(app.fam_cn, 10)).pack(side="left")
        self.var_watch_grace = tk.StringVar(
            value="%g" % float(wc.get("grace_min") or 10))
        tk.Entry(row4, textvariable=self.var_watch_grace, width=5, justify="center",
                 font=(app.fam_num, 10, "bold"), bg="#FFFBF2", fg=pal["ink"],
                 relief="flat", insertbackground=pal["seal"],
                 highlightthickness=1, highlightbackground=pal["border_soft"],
                 highlightcolor=pal["seal"]).pack(side="left", padx=(4, 4), ipady=3)
        self._wrap(tk.Label(row4, text="分钟。这十分钟里反复确认它确实不在，才寄信"
                                        "（一出现就自动撤销）",
                            bg=pal["paper"], fg=pal["ink"],
                            font=(app.fam_cn, 10), anchor="w", justify="left"), 118).pack(
            side="left")

        bar = tk.Frame(wrap, bg=pal["paper"])
        bar.pack(fill="x", pady=(8, 0))
        probe = tk.Label(bar, text="看一眼它现在在不在", bg=pal["paper"], fg=pal["ink"],
                         font=(app.fam_cn, 10), cursor="hand2",
                         padx=12, pady=3, highlightthickness=1,
                         highlightbackground=pal["border_soft"])
        probe.pack(side="left")
        probe.bind("<Button-1>", lambda e: self._probe_watch_now())
        probe.bind("<Enter>", lambda e: probe.configure(fg=pal["seal"]))
        probe.bind("<Leave>", lambda e: probe.configure(fg=pal["ink"]))

        # 「试一遍」是给「等不了半小时、想当场看见效果」的人准备的：
        # 它假装那扇窗刚不见，把问话窗和寄信整条路真走一遍（真的会发信）。
        # 光有一个「现在就检查一次」是不够的 —— 那只会回一句「窗口在」，
        # 用户还是不知道出事之后到底会发生什么。
        drill = tk.Label(bar, text="试一遍（假装它不见了）", bg="#FFFBF2",
                         fg=pal["seal"], font=(app.fam_cn, 10, "bold"),
                         cursor="hand2", padx=12, pady=3,
                         highlightthickness=1, highlightbackground=pal["seal"])
        drill.pack(side="left", padx=(8, 0))
        drill.bind("<Button-1>", lambda e: self._drill_watch_now())
        drill.bind("<Enter>", lambda e: drill.configure(bg=pal["seal"], fg="#FFF8EC"))
        drill.bind("<Leave>", lambda e: drill.configure(bg="#FFFBF2", fg=pal["seal"]))

        self.watch_msg = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                            fg=pal["ink_soft"], font=(app.fam_cn, 9),
                                            anchor="w", justify="left"), 40)
        self.watch_msg.pack(fill="x", pady=(6, 0))

        self.watch_state_lbl = self._wrap(tk.Label(wrap, text="", bg=pal["paper"],
                                                  fg=pal["ink_soft"],
                                                  font=(app.fam_cn, 9),
                                                  anchor="w", justify="left"), 40)
        self.watch_state_lbl.pack(fill="x", pady=(6, 0))

        if not app.notify_configured():
            self._wrap(tk.Label(wrap, text="　⚠ 上面的「传书」还没配好邮箱，"
                                           "窗口不见了也寄不出去。",
                                bg=pal["paper"], fg=pal["seal"], font=(app.fam_cn, 9),
                                anchor="w", justify="left"), 40).pack(fill="x", pady=(2, 0))

        self._reload_window_list(False)
        self._sync_watch_status()
        self._poll_watch()

    def _reload_window_list(self, verbose=False):
        """把「此刻开着的窗口」填进下拉框。只在这里枚举 —— 那要几毫秒，不必每秒做。"""
        titles = list_windows()
        menu = self.win_pick["menu"]
        menu.delete(0, "end")
        if not titles:
            menu.add_command(label="（没找到可见窗口）", command=lambda: None)
        for title in titles:
            menu.add_command(label=title,
                             command=lambda v=title: self._pick_window(v))
        self.var_pick.set("（点这里挑一个）")
        if verbose and hasattr(self, "watch_msg"):
            if titles:
                self.watch_msg.configure(text="列出了 %d 扇窗，挑一个" % len(titles),
                                         fg=self.pal["ink_soft"])
            else:
                self.watch_msg.configure(text="没找到可见窗口（要先把游戏开起来）",
                                         fg=self.pal["seal"])

    def _pick_window(self, title):
        """从下拉框挑了一扇：填进关键字框，用户还能接着改短。"""
        self.var_pick.set(title)
        self.entry_watch.delete(0, "end")
        self.entry_watch.insert(0, title)
        self.watch_msg.configure(text="已选：%s" % title[:40], fg=self.pal["ink_soft"])

    def _probe_watch_now(self):
        """立刻看一眼：不推进状态机，只让用户当场知道认不认得出这扇窗。"""
        kw = self.entry_watch.get().strip()
        if not kw:
            self.watch_msg.configure(text="先挑一扇窗，或者手填一段关键字",
                                     fg=self.pal["seal"])
            return
        titles = list_windows()
        hit = None
        key = _squeeze(kw)
        for title in titles:
            if key and key in _squeeze(title):
                hit = title
                break
        if hit:
            self.watch_msg.configure(
                text="现在能看到它：%s　（真出事是什么样子，点右边「试一遍」演给你看）"
                     % hit[:32], fg="#4F7A52")
        else:
            self.watch_msg.configure(
                text="现在看不到这个窗口。若它本来就还没开，这是正常的 —— "
                     "程序要「先看见过一次」才开始盯，否则每次开机都会白寄一封信。",
                fg=self.pal["seal"])

    def _drill_watch_now(self):
        """「试一遍」：假装窗口刚不见，把整条路真走一遍（会真发一封演练信）。"""
        kw = self.entry_watch.get().strip()
        if not kw:
            self.watch_msg.configure(text="先挑一扇窗（演练也拿它当信里的名字）",
                                     fg=self.pal["seal"])
            return
        if not self.app.notify_configured():
            self.watch_msg.configure(
                text="邮箱还没配好，演练也发不出去 —— 先去「传书」那一节把邮箱填上。",
                fg=self.pal["seal"])
            return
        self.app.watch_drill(kw)
        self.watch_msg.configure(
            text="演练开始：桌面上冒出一扇问话窗，%d 秒没人理会就真寄一封"
                 "标注为「演练」的信给你。" % WATCH_DRILL_SEC,
            fg=self.pal["seal"])

    def _sync_watch_status(self):
        if not hasattr(self, "watch_state_lbl"):
            return
        try:
            self.watch_state_lbl.configure(
                text="　现在：%s" % self.app.watch_status_text())
        except tk.TclError:
            pass

    def _poll_watch(self):
        """
        每秒钟把盯守状态与「距关机还有多久」重写一遍。

        只读内存，不枚举窗口，开销可忽略。借这个轮询顺手刷关机那一行 ——
        两处都要「每秒变一次」的效果，没必要各养一条 after 链。
        """
        try:
            if not self.win.winfo_exists():
                return
            self._sync_watch_status()
            self._sync_shutdown_note()
            self.win.after(1000, self._poll_watch)
        except tk.TclError:
            return          # 面板已经关了，轮询自然停下

    def _collect_watch(self):
        try:
            interval = int(float(self.var_interval.get().strip() or 30))
        except ValueError:
            return None, "「每隔几分钟看一眼」要填数字"
        if not WATCH_PROBE_MIN <= interval <= WATCH_PROBE_MAX:
            return None, "巡检间隔要在 %d ~ %d 分钟之间" % (WATCH_PROBE_MIN,
                                                         WATCH_PROBE_MAX)

        try:
            grace = int(float(self.var_watch_grace.get().strip() or 10))
        except ValueError:
            return None, "「连续不见几分钟才寄信」要填数字"
        if not WATCH_GRACE_MIN <= grace <= WATCH_GRACE_MAX:
            return None, "「连续不见几分钟」要在 %d ~ %d 之间" % (WATCH_GRACE_MIN,
                                                             WATCH_GRACE_MAX)

        title = self.entry_watch.get().strip()
        if self.var_watch.get() and not title:
            return None, "开了窗口盯守，得先挑一扇要盯的窗口"

        return {"enabled": bool(self.var_watch.get()),
                "title": title,
                "interval_min": interval,
                "grace_min": grace}, None

    def _build_shared(self, parent):
        """
        「多机共用设置」一节。

        为什么放在面板里而不是做成命令行参数：会用这个功能的人手上有十来台
        机器要配成一样，他不会为了这个去开命令行。面板里点一下导出、
        把文件拷过去、在对方机器上导入，三步就完事。
        """
        app, pal = self.app, self.pal
        self._section("多机共用设置", parent)


        self._wrap(tk.Label(parent,
                            text="　把设置导成一份文件，拷到别的机器上；在那台机器的设置面板里\n"
                                 "　点「从文件导入…」选中它，即刻生效（那份文件会留着，不删）。",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(
            fill="x", padx=18, pady=(3, 0))
        self._wrap(tk.Label(parent,
                            text="　导出时可以一项一项挑 —— 不挑的那项，对方机器上原样保留。",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(
            fill="x", padx=18, pady=(1, 0))
        self._wrap(tk.Label(parent,
                            text="　本机抬头与开机自启不在文件里 —— 每台机器各自设。",
                            bg=pal["paper"], fg=pal["border"], font=(app.fam_cn, 9),
                            anchor="w", justify="left"), 40).pack(
            fill="x", padx=18, pady=(1, 0))

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
        self.lbl_shared = self._wrap(tk.Label(parent, text="　" + tip, bg=pal["paper"],
                                              fg=color, font=(app.fam_cn, 9),
                                              anchor="w", justify="left"), 40)
        self.lbl_shared.pack(fill="x", padx=18, pady=(6, 0))

    def _build_footer(self):
        pal = self.pal
        tk.Frame(self.body, bg=pal["border_soft"], height=1).pack(
            fill="x", padx=18, pady=(14, 0))
        bar = tk.Frame(self.body, bg=pal["paper"])
        bar.pack(fill="x", padx=18, pady=12)
        # 开头先摆一句发现性提示：右下角那个角能拖，不说出来没人会去试。
        # 之后任何一次操作反馈都会把它顶掉，不会长期占着地方。
        self.msg = tk.Label(bar, text="右下角可拖动改面板大小", bg=pal["paper"],
                            fg=pal["border"], font=(self.app.fam_cn, 10))
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

        # 定时关机与窗口盯守：两块各自校验，任一处填错就整份不保存 ——
        # 半份保存最难查（用户以为存上了，实际只有一半生效）。
        shut_cfg, err = self._collect_shutdown()
        if err:
            self.msg.configure(text=err)
            return
        watch_cfg, err = self._collect_watch()
        if err:
            self.msg.configure(text=err)
            return
        remote_cfg, remote_creds, err = self._collect_remote()
        if err:
            self.msg.configure(text=err)
            return

        # 自动检查开关不动 apply_settings 的签名（那会牵动一圈调用点），
        # 直接改在 cfg 上 —— apply_settings 末尾本来就会 save_config 落盘。
        self.app.cfg["auto_update_check"] = bool(self.var_autoupd.get())

        # 远程设置的密码 / 令牌跟邮箱授权码走同一个凭据段 ——
        # 同一套加密、同一套「永不参与同步」的待遇。
        secret = dict(secret or {})
        secret.update(remote_creds)

        err = self.app.apply_settings(self.entry.get(), thresholds,
                                      self.var_lock.get(), self.var_top.get(),
                                      self.var_autostart.get(),
                                      notify_cfg, secret,
                                      extra_cfg={"shutdown": shut_cfg,
                                                 "watch": watch_cfg,
                                                 "remote": remote_cfg})
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
            "　· 窗口位置与大小\n"
            "　· 定时关机的网址、窗口盯守的设置与盯守状态\n\n"
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
        """
        把一段界面操作排到主线程去执行。

        除了 TclError，还要吞 RuntimeError：没有跑 mainloop 的时候
        （自检脚本就是这种），`after` 内部 createcommand 会抛
        「main thread is not in main loop」。语义上我们只想要「排得上就排，
        排不上就算了」，两种异常都该咽下去 —— 不然自检输出里会多出一段
        红色堆栈，让人以为哪里坏了。
        """
        try:
            self.win.after(0, fn)
        except (tk.TclError, RuntimeError):
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
        # 尺寸记一笔。放在关窗这里而不是拖完那一刻，是为了不打断
        # 「设置要点保存才作数」这条规矩（见 _remember_panel_size）。
        if self._resized:
            self._remember_panel_size()
        try:
            self.win.destroy()
        except tk.TclError:
            pass

    # ---- 杂项 ----

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


class ShutdownAlertWindow:
    """
    「马上要关机」那扇问话窗。

    为什么要有它：两个来源（网址取回的时刻 / 倒计时归零）谁先到就关，
    那一刻用户多半不在机器前 —— 但万一他正坐在那儿，得给他一个反悔的
    机会，否则一次「到点」就把他手里的活直接掀了。

    三件事同时成立，这扇窗才算做对了：
      · 没人理它时，倒计时走完**照关** —— 无人值守走的就是这条路，
        这也是它和盯守那扇窗唯一方向相反的地方（盯守默认「寄信」，
        这扇默认「关机」）；
      · 关窗 / 按 Esc 也算「没表态」，照关。默认偏「关」的理由：用户开这个
        功能图的就是到点能停下来，「因为没点到按钮所以没关」反而是故障；
      · 置顶**并且抢一次键盘焦点** —— 和盯守那扇刻意不抢焦点相反：
        那扇多寄一封信，这扇是机器要关了，必须让人立刻看见。
    """

    def __init__(self, app, when, source, wait_sec, drill=False):
        self.app = app
        self.when = when
        self.source = source or "remote"
        self.drill = bool(drill)
        self.deadline = time.time() + max(0, int(wait_sec))
        self.done = False
        pal = app.cfg["palette"]
        self.pal = pal
        label = dict(SHUTDOWN_SOURCES).get(self.source, self.source)

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)

        body = tk.Frame(self.win, bg=pal["paper"])
        body.pack(fill="both", expand=True, padx=3, pady=3)

        # 抬头用「印泥色」而不是盯守那种墨色：一眼就能分清「这扇是要关机的」。
        head = tk.Frame(body, bg=pal["seal"], height=34)
        head.pack(fill="x")
        head.pack_propagate(False)
        tk.Label(head, text="　定 时 关 机 · 演练" if self.drill
                 else "　定 时 关 机 · 就要关机了",
                 bg=pal["seal"], fg="#FFF8EC",
                 font=(app.fam_cn, 11, "bold")).pack(side="left", padx=10)
        closer = tk.Label(head, text="✕", bg=pal["seal"], fg="#FFF8EC",
                          font=("Segoe UI", 10), cursor="hand2", padx=12)
        closer.pack(side="right", fill="y")
        closer.bind("<Button-1>", lambda e: self.finish(True))

        wrap = tk.Frame(body, bg=pal["paper"])
        wrap.pack(fill="both", expand=True, padx=22, pady=16)

        tk.Label(wrap, text=("演练：假装下面这个时刻刚刚到了 ——" if self.drill
                             else "下面这个时刻到了："),
                 bg=pal["paper"], fg=pal["ink_soft"], font=(app.fam_cn, 10),
                 anchor="w").pack(fill="x")
        tk.Label(wrap, text="%s　%s" % (label, pretty_target(self.when)),
                 bg=pal["paper"], fg=pal["ink"], font=(app.fam_cn, 12, "bold"),
                 anchor="w", justify="left",
                 wraplength=440).pack(fill="x", pady=(2, 0))

        self.count = tk.Label(wrap, text="", bg=pal["paper"], fg=pal["seal"],
                              font=(app.fam_num, 24, "bold"), anchor="w")
        self.count.pack(fill="x", pady=(10, 0))

        # 注意别在这里写 Markdown 的星号 —— Tk 的 Label 不认，会把星号原样打出来。
        tk.Label(wrap, text=(
            "演练到此为止 —— 倒计时走完什么都不会发生，不会真关机。"
            "两颗按钮都可以点，看看它们各自是什么反应。"
            if self.drill else
            "不点下面那颗按钮的话，倒计时走完就立刻关机。"
            "关不掉的话每分钟会自动再试一次，直到关掉为止。"),
            bg=pal["paper"], fg=pal["ink"], font=(app.fam_cn, 10),
            anchor="w", justify="left", wraplength=440).pack(fill="x", pady=(4, 0))

        bar = tk.Frame(wrap, bg=pal["paper"])
        bar.pack(fill="x", pady=(14, 0))
        mine = tk.Label(bar, text="先不关，留着电脑", bg=pal["seal"], fg="#FFF8EC",
                        font=(app.fam_cn, 11, "bold"), cursor="hand2",
                        padx=18, pady=7)
        mine.pack(side="left")
        mine.bind("<Button-1>", lambda e: self.finish(False))
        mine.bind("<Enter>", lambda e: mine.configure(bg=pal["ink"]))
        mine.bind("<Leave>", lambda e: mine.configure(bg=pal["seal"]))

        now = tk.Label(bar, text=("就按「关」来一遍" if self.drill
                                  else "不用等了，现在就关"),
                       bg=pal["paper"], fg=pal["ink_soft"],
                       font=(app.fam_cn, 11), cursor="hand2", padx=16, pady=7)
        now.pack(side="left", padx=(8, 0))
        now.bind("<Button-1>", lambda e: self.finish(True))
        now.bind("<Enter>", lambda e: now.configure(fg=pal["seal"]))
        now.bind("<Leave>", lambda e: now.configure(fg=pal["ink_soft"]))

        self.win.bind("<Escape>", lambda e: self.finish(True))

        self.win.update_idletasks()
        w = max(500, self.win.winfo_reqwidth())
        h = self.win.winfo_reqheight()
        sw, sh = self.win.winfo_screenwidth(), self.win.winfo_screenheight()
        set_geometry(self.win, w, h, (sw - w) // 2, max(20, (sh - h) // 3))
        self._grab_focus()
        self._tick()

    # ---- 生命周期 ----

    def _grab_focus(self):
        """
        抢一次焦点，并响一声。

        和盯守那扇窗刻意相反：那扇不抢（会把人从全屏游戏里顶出来，
        代价不过是一封信），这扇必须抢 —— 机器马上要关，漏掉就是丢工作。
        """
        try:
            self.win.deiconify()
            self.win.lift()
            self.win.attributes("-topmost", True)
            self.win.focus_force()
            self.win.bell()
        except tk.TclError:
            pass

    def alive(self):
        try:
            return bool(self.win.winfo_exists())
        except tk.TclError:
            return False

    def lift(self):
        self._grab_focus()

    def _tick(self):
        """每秒改写一次倒计时。到点就按「没人反对」处理 —— 直接关。"""
        if self.done:
            return
        left = int(self.deadline - time.time())
        if left <= 0:
            self.finish(True)
            return
        self.count.configure(
            text=("演练：还有 %d 分 %02d 秒结束" if self.drill
                  else "还有 %d 分 %02d 秒就关机") % (left // 60, left % 60))
        try:
            self.win.after(500, self._tick)
        except tk.TclError:
            pass

    def finish(self, proceed):
        """proceed=True 就是「照关」。点按钮、超时、关窗、Esc 全走这里。"""
        if self.done:
            return
        self.done = True
        try:
            self.win.destroy()
        except tk.TclError:
            pass
        if getattr(self.app, "_shutdown_win", None) is self:
            self.app._shutdown_win = None
        try:
            self.app.shutdown_alert_done(bool(proceed), drill=self.drill)
        except Exception as exc:                      # noqa: BLE001
            # 这一步会去发关机命令，出岔子必须留痕 —— 窗口已经没了，
            # 用户能看到的只有「机器没关」。
            log_problem("关机确认", type(exc), exc, exc.__traceback__)

    def close(self):
        """
        程序退出 / 用户从右键菜单取消时把窗收掉。

        刻意**不走 finish**：那会去发关机命令，而这两条路都是「不要关」。
        状态由调用方负责归位（shutdown_cancel_now / quit_app）。
        """
        self.done = True
        try:
            self.win.destroy()
        except tk.TclError:
            pass
        if getattr(self.app, "_shutdown_win", None) is self:
            self.app._shutdown_win = None


class WatchAlertWindow:
    """
    「窗口不见了」那扇问话窗。

    为什么要有它：这台机器通常没人守着，窗口没了（掉线、崩了、被谁关了）
    必须有人立刻知道，所以默认是**要寄信的**。可万一用户就坐在机器前、
    是他自己关的游戏，那封信就是纯骚扰 —— 于是留几秒钟让他点一下
    「是我关的，不必寄信」。

    三件事同时成立，这扇窗才算做对了：
      · 没人理它时，倒计时走完自动寄信 —— 无人值守走的就是这条路；
      · 关掉窗口 / 按 Esc 也算「没确认」，照寄。默认偏「寄」：漏报
        （该响没响）比误报（给你白寄一封信）贵得多；
      · 置顶，但**不抢键盘焦点** —— 用户正在玩游戏时不该被它顶出全屏。
    """

    def __init__(self, app, pend, drill=False):
        self.app = app
        self.pend = pend or {}
        self.drill = bool(drill)
        # 这扇窗占 app 上哪个槽 —— 真出事占 _alert_win，演练占 _drill_win。
        # 分开的理由：两者可能同时存在（用户点了演练，恰好这时游戏真掉了），
        # 挤在同一个槽里会互相顶掉，谁先关就都不知道了。
        self.slot = "_drill_win" if self.drill else "_alert_win"
        self.done = False
        pal = app.cfg["palette"]
        self.pal = pal

        self.win = tk.Toplevel(app.root)
        self.win.overrideredirect(True)
        self.win.configure(bg=pal["border"])
        self.win.attributes("-topmost", True)

        body = tk.Frame(self.win, bg=pal["paper"])
        body.pack(fill="both", expand=True, padx=3, pady=3)

        head = tk.Frame(body, bg=pal["ink"], height=34)
        head.pack(fill="x")
        head.pack_propagate(False)
        tk.Label(head, text="　盯 守 · 演练" if self.drill else "　盯 守 · 窗口不见了",
                 bg=pal["ink"], fg=pal["paper"],
                 font=(app.fam_cn, 11, "bold")).pack(side="left", padx=10)
        closer = tk.Label(head, text="✕", bg=pal["ink"], fg=pal["border_soft"],
                          font=("Segoe UI", 10), cursor="hand2", padx=12)
        closer.pack(side="right", fill="y")
        closer.bind("<Button-1>", lambda e: self.finish(True))

        wrap = tk.Frame(body, bg=pal["paper"])
        wrap.pack(fill="both", expand=True, padx=22, pady=16)

        tk.Label(wrap, text=("演练：假装这扇窗口刚刚不见了 ——" if self.drill
                             else "你盯着的那扇窗口不见了："),
                 bg=pal["paper"], fg=pal["ink_soft"], font=(app.fam_cn, 10),
                 anchor="w").pack(fill="x")
        tk.Label(wrap, text=self.pend.get("keyword") or "—", bg=pal["paper"],
                 fg=pal["ink"], font=(app.fam_cn, 12, "bold"),
                 anchor="w", justify="left", wraplength=420).pack(fill="x", pady=(2, 0))

        info = ["发现时间　%s" % (self.pend.get("at") or _stamp()),
                "上次见到　%s" % (self.pend.get("seen_at") or "—"),
                "检查间隔　每 %d 分钟看一眼" % int(self.pend.get("interval_min") or 30)]
        if not self.drill:
            # 真实盯守：这十分钟是「反复核实过它确实不在」的十分钟 ——
            # 说清楚，用户才知道为什么值得等（以及它回来了会怎样）。
            info.append("寄信条件　连续不见 %d 分钟（期间反复核实）"
                        % int(self.pend.get("minutes") or 10))
        tk.Label(wrap, text="\n".join(info), bg=pal["paper"], fg=pal["ink_soft"],
                 font=(app.fam_cn, 9), anchor="w", justify="left").pack(fill="x",
                                                                       pady=(8, 0))

        self.count = tk.Label(wrap, text="", bg=pal["paper"], fg=pal["seal"],
                              font=(app.fam_num, 24, "bold"), anchor="w")
        self.count.pack(fill="x", pady=(10, 0))
        tk.Label(wrap, text=("演练到此为止都还不用管它；倒计时走完会真发一封"
                             "标注为「演练」的信给你，验证寄信这条路通不通。"
                             if self.drill else
                             "没人点下面那颗按钮的话，倒计时走完就自动寄信给你；"
                             "这十分钟里它又出现，就当场撤销，不当它消失过。"),
                 bg=pal["paper"], fg=pal["ink"], font=(app.fam_cn, 10),
                 anchor="w", justify="left", wraplength=420).pack(fill="x", pady=(4, 0))

        bar = tk.Frame(wrap, bg=pal["paper"])
        bar.pack(fill="x", pady=(14, 0))
        mine = tk.Label(bar, text="不寄，结束演练" if self.drill else "是我关的，不必寄信",
                        bg=pal["seal"], fg="#FFF8EC",
                        font=(app.fam_cn, 11, "bold"), cursor="hand2", padx=18, pady=7)
        mine.pack(side="left")
        mine.bind("<Button-1>", lambda e: self.finish(False))
        mine.bind("<Enter>", lambda e: mine.configure(bg=pal["ink"]))
        mine.bind("<Leave>", lambda e: mine.configure(bg=pal["seal"]))

        now = tk.Label(bar, text="现在就寄这一封" if self.drill else "现在就寄",
                       bg=pal["paper"], fg=pal["ink_soft"],
                       font=(app.fam_cn, 11), cursor="hand2", padx=16, pady=7)
        now.pack(side="left", padx=(8, 0))
        now.bind("<Button-1>", lambda e: self.finish(True))
        now.bind("<Enter>", lambda e: now.configure(fg=pal["seal"]))
        now.bind("<Leave>", lambda e: now.configure(fg=pal["ink_soft"]))

        self.win.bind("<Escape>", lambda e: self.finish(True))

        self.win.update_idletasks()
        w = max(470, self.win.winfo_reqwidth())
        h = self.win.winfo_reqheight()
        sw, sh = self.win.winfo_screenwidth(), self.win.winfo_screenheight()
        set_geometry(self.win, w, h, (sw - w) // 2, max(20, (sh - h) // 3))
        self._tick()

    # ---- 生命周期 ----

    def alive(self):
        try:
            return bool(self.win.winfo_exists())
        except tk.TclError:
            return False

    def lift(self):
        try:
            self.win.lift()
            self.win.attributes("-topmost", True)
        except tk.TclError:
            pass

    def _tick(self):
        """每秒改写一次倒计时。到点就按「没人应答」处理 —— 直接寄信。"""
        if self.done:
            return
        left = int(float(self.pend.get("deadline_ts") or 0) - time.time())
        if left <= 0:
            self.finish(True)
            return
        self.count.configure(
            text=(("还有 %d 分 %02d 秒自动寄出演练信" if self.drill
                   else "还有 %d 分 %02d 秒自动寄信") % (left // 60, left % 60)))
        try:
            self.win.after(500, self._tick)
        except tk.TclError:
            pass

    def finish(self, send):
        if self.done:
            return
        self.done = True
        try:
            self.win.destroy()
        except tk.TclError:
            pass
        # 从 app 上对应的槽里摘掉自己（真出事是 _alert_win，演练是 _drill_win）
        if getattr(self.app, self.slot, None) is self:
            setattr(self.app, self.slot, None)
        try:
            self.app.finish_watch_alert(bool(send), self.pend)
        except Exception as exc:                      # noqa: BLE001
            # 这一步会去派生发信进程，出岔子也得留痕 —— 窗口已经没了，
            # 用户能看到的只有「信没来」。
            log_problem("盯守确认", type(exc), exc, exc.__traceback__)

    def close(self):
        """
        程序退出时把窗收掉。

        刻意**不走 finish**：那会去寄信。用户是主动退程序的，
        不该因为退程序而多出一封信；状态留在注册表里，下次启动接着问。
        """
        self.done = True
        try:
            self.win.destroy()
        except tk.TclError:
            pass
        if getattr(self.app, self.slot, None) is self:
            setattr(self.app, self.slot, None)


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
    migrate_legacy_files()   # 老数据（注册表 / exe 旁边的旧 json）搬进新配置文件（一次性）
    # 这里曾经会在启动时扫 exe 旁边有没有共用设置文件、有就读走并删掉
    # （v1.6 起去掉了 —— 见 apply_shared_file 的说明）。现在导入只走设置面板
    # 那条路：什么时候导、导哪一份，都由用户当场挑，程序不擅自改设置。
    app = CountdownApp()
    app.run()


if __name__ == "__main__":
    sys.exit(main())
