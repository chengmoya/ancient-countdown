#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
传书使者 · mailer
==================
被主程序以「独立进程」拉起的发信脚本。

为什么要单开一个进程
  smtplib + email 两个模块导入起来要几 MB，而 SMTP 握手碰上网络不畅
  最长能卡 20 多秒。如果放在主程序里，常驻内存会变大，网络一慢窗口
  还会失去响应。派生进程的代价只在这一瞬间 —— 发完就退出，
  主程序的占用立刻回到原样。

怎么被调用（由 AncientCountdown.pyw 自动完成，不需要手动运行）
  pythonw mailer.pyw
  从注册表读任务（notify_task），寄出后把结果写回注册表（notify_result）。

退出码
  0 = 寄出成功    1 = 寄出失败    2 = 任务缺失或损坏
"""

import json
import os
import smtplib
import ssl
import sys
import winreg
from email.message import EmailMessage
from email.utils import formataddr

# 数据仓在注册表里。键名由主程序通过环境变量指定（带演练隔离后缀），
# 拿不到 env 就用默认键 —— 源码模式手工调用时读写的正是真实数据。
REGKEY = os.environ.get("ANCIENT_COUNTDOWN_REGKEY") or r"Software\AncientCountdown"
TASK_NAME = "notify_task"
RESULT_NAME = "notify_result"
TEST_RESULT_NAME = "notify_test_result"
TIMEOUT = 25.0          # 单次网络操作上限，避免进程僵在那里
ERR_LIMIT = 300


def _reg_value(name):
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, REGKEY, 0,
                            winreg.KEY_READ) as key:
            raw, _ = winreg.QueryValueEx(key, name)
        return json.loads(raw)
    except (OSError, ValueError):
        return None


def _set_reg_value(name, data):
    try:
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, REGKEY) as key:
            winreg.SetValueEx(key, name, 0, winreg.REG_SZ,
                              json.dumps(data, ensure_ascii=False))
        return True
    except OSError:
        return False


def _del_reg_value(name):
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, REGKEY, 0,
                            winreg.KEY_SET_VALUE) as key:
            winreg.DeleteValue(key, name)
    except OSError:
        pass


def write_result(name, token, ok, error=""):
    """把结果写回注册表。主程序下一轮巡检会来取走。"""
    payload = {"token": token, "ok": bool(ok), "error": (error or "")[:ERR_LIMIT]}
    _set_reg_value(name, payload)


def read_task():
    task = _reg_value(TASK_NAME)
    if not isinstance(task, dict):
        raise ValueError("task missing or damaged")
    return task


def drop_task():
    """任务里带着授权码，无论成败都要立刻抹掉。"""
    _del_reg_value(TASK_NAME)


def build_message(task, user):
    """user 由调用方从 task["smtp"]["user"] 取出后传入。
    早先这里写的是 task["user"] —— 而任务文件里 user 嵌在 smtp 之下，
    取错层级会抛 KeyError('user')，报错文字就是光秃秃的 'user'。
    所以改成显式传参，让这个取值只有一处来源。"""
    msg = EmailMessage()
    # 发件人显示名用「本机抬头」：收件箱里不用点开就能看出是哪台机器寄的。
    # 抬头留空时退回程序名，保持老样子。换行必须滤掉，否则等于往邮件头注入字段。
    shown = (task.get("from_name") or "").replace("\r", "").replace("\n", "").strip()
    msg["From"] = formataddr((shown or "古风倒计时", user))
    msg["To"] = task["to"]
    msg["Subject"] = task["subject"]
    msg.set_content(task["body"], charset="utf-8")
    return msg


def looks_like_mail(addr):
    """粗校验邮箱地址的形状。宁可在这里拦下来，也别去让服务器甩一句英文。"""
    addr = (addr or "").strip()
    if not addr or " " in addr or addr.count("@") != 1:
        return False
    local, _, domain = addr.partition("@")
    if not local or not domain:
        return False
    # 域名必须有点，且不能以点开头/结尾 —— 少写一个点正是最常见的笔误
    if "." not in domain or domain.startswith(".") or domain.endswith("."):
        return False
    return True


def deliver(task):
    smtp = task["smtp"]
    host = smtp["host"]
    port = int(smtp["port"])
    user = smtp["user"]
    password = smtp["password"]
    msg = build_message(task, user)


    if smtp.get("use_ssl", True):
        ctx = ssl.create_default_context()
        with smtplib.SMTP_SSL(host, port, timeout=TIMEOUT, context=ctx) as srv:
            srv.login(user, password)
            srv.send_message(msg)
    else:
        # 587 这类端口走 STARTTLS：先明文握手，再升级为加密
        ctx = ssl.create_default_context()
        with smtplib.SMTP(host, port, timeout=TIMEOUT) as srv:
            srv.ehlo()
            srv.starttls(context=ctx)
            srv.ehlo()
            srv.login(user, password)
            srv.send_message(msg)


def friendly(err):
    """
    把底层报错翻译成一句人话，后面再附上原文备查。

    判定有先后：越具体的规则越靠前。
    早先把 'auth' 这个宽泛词放在前面，结果 QQ 的
    "mail from address must be same as authorization user" 被误判成
    「登录被拒、要填授权码」，把使用者往错方向引 —— 那条其实是地址不一致。
    """
    text = "%s" % err
    low = text.lower()

    # 先挡一类「程序自身出错」：KeyError 的字符串形式就是带引号的光杆字段名
    if text.startswith("'") and text.endswith("'") and " " not in text:
        return "程序内部出错（缺少字段 %s），这是脚本缺陷，请把这句话反馈。" % text

    if "must be same as authorization user" in low or "sender address rejected" in low:
        return "发件邮箱和登录账号不是同一个 —— 这两处要填完全一样的地址。" + text
    if "invalid user" in low or "user unknown" in low or "no such user" in low \
            or "unknown user" in low:
        return "对方服务器说没有这个邮箱账号 —— 地址可能写错或不存在。" + text
    if "authorizationcode" in low or "535" in text \
            or "authentication failed" in low or "login fail" in low:
        return "登录被拒 —— 多半填成了登录密码。这里要填邮箱的「授权码」。" + text
    if "unexpectedly closed" in low or "connection reset" in low \
            or "disconnected" in low or "eof occurred" in low:
        return "服务器把连接直接断开了 —— 常见于邮箱地址不完整（比如少写一个点），" \
               "也可能是短时间连太频繁被限流，稍后再试。" + text
    if "getaddrinfo" in low or "name or service" in low or "11001" in text:
        return "找不到邮件服务器 —— 检查网络，或确认服务器地址没写错。" + text
    if "timed out" in low or "timeout" in low:
        return "连接邮件服务器超时 —— 网络不通，或防火墙拦住了端口。" + text
    if "ssl" in low or "certificate" in low or "wrong version" in low:
        return "加密方式不匹配 —— SSL 通常配 465 端口，STARTTLS 配 587。" + text
    if "550" in text or "553" in text or "relay" in low:
        return "被对方拒收 —— 收件地址可能写错了。" + text
    return text


def main():
    try:
        task = read_task()
    except Exception:                            # noqa: BLE001
        drop_task()
        return 2

    token = task.get("token", "")
    smtp = task.get("smtp") or {}
    # 试寄模式把结果写到另一个值：正式通知的履历不该被一次试验污染，
    # 两者也可能同时存在，共用一个值会互相抢
    test_mode = len(sys.argv) > 1 and sys.argv[1] == "test"
    result_name = TEST_RESULT_NAME if test_mode else RESULT_NAME

    if not smtp.get("user") or not smtp.get("password"):
        write_result(result_name, token, False, "发件邮箱或授权码为空，还没配置完整。")
        drop_task()
        return 1

    if not task.get("to"):
        write_result(result_name, token, False, "收件地址为空。")
        drop_task()
        return 1

    # 先在本地把地址形状查一遍。畸形地址若放过去，服务器多半只回一句英文、
    # 甚至直接掐断连接，使用者根本看不出是自己少写了一个点。
    sender = (smtp.get("user") or "").strip()
    if not looks_like_mail(sender):
        write_result(result_name, token, False,
                     "发件邮箱地址看着不完整：%s —— 检查是不是少写了一个点。" % sender)
        drop_task()
        return 1
    rcpt = (task.get("to") or "").strip()
    if not looks_like_mail(rcpt):
        write_result(result_name, token, False,
                     "收件邮箱地址看着不完整：%s —— 检查是不是少写了一个点。" % rcpt)
        drop_task()
        return 1

    try:
        deliver(task)
    except Exception as exc:                     # noqa: BLE001
        write_result(result_name, token, False, friendly(exc))
        drop_task()
        return 1

    write_result(result_name, token, True, "")
    drop_task()
    return 0


if __name__ == "__main__":
    sys.exit(main())
