@echo off
rem ============================================================
rem  古风倒计时 - 启动脚本
rem  双击本文件即可运行；不会弹出黑色命令窗口残留
rem ============================================================
cd /d "%~dp0"
setlocal enabledelayedexpansion

set "SCRIPT=AncientCountdown.pyw"
set "PYW="

rem 1) 本机 Python 3.14 默认安装位置
if exist "C:\Python314\pythonw.exe" set "PYW=C:\Python314\pythonw.exe"

rem 2) 其他常见安装位置
if not defined PYW if exist "%LOCALAPPDATA%\Programs\Python\Python313\pythonw.exe" set "PYW=%LOCALAPPDATA%\Programs\Python\Python313\pythonw.exe"
if not defined PYW if exist "%LOCALAPPDATA%\Programs\Python\Python312\pythonw.exe" set "PYW=%LOCALAPPDATA%\Programs\Python\Python312\pythonw.exe"

rem 3) 从 PATH 中查找
if not defined PYW for /f "delims=" %%i in ('where pythonw 2^>nul') do (
    if not defined PYW set "PYW=%%i"
)

rem 4) 通过 py 启动器启动
if not defined PYW (
    where py >nul 2>nul && (
        start "" pyw "%SCRIPT%"
        exit /b 0
    )
    echo.
    echo   [错误] 没有找到 Python 运行环境。
    echo   请安装 Python 3.10 及以上版本：https://www.python.org/downloads/
    echo   安装时请勾选 "Add python.exe to PATH"。
    echo.
    pause
    exit /b 1
)

start "" "%PYW%" "%SCRIPT%"
exit /b 0
