@echo off
echo ===================================
echo BOM检查工具依赖安装程序
echo ===================================
echo.

REM 检查Python是否已安装
python --version > nul 2>&1
if %errorlevel% neq 0 (
    echo 错误: 未找到Python！请先安装Python 3.6或更高版本。
    echo 您可以从https://www.python.org/downloads/下载Python。
    echo.
    pause
    exit /b 1
)

echo 检测到Python已安装，正在安装依赖...
echo.

REM 尝试安装依赖
echo 步骤 1/5: 安装pandas...
pip install pandas

echo 步骤 2/5: 安装pymupdf...
pip install pymupdf

echo 步骤 3/5: 安装openpyxl...
pip install openpyxl

echo 步骤 4/5: 安装pillow...
pip install pillow

echo 步骤 5/5: 安装psutil...
pip install psutil

echo.
echo ===================================
echo 所有依赖安装完成！
echo.
echo 如果以上安装过程中出现错误，请尝试以管理员身份运行此脚本。
echo 方法：右键点击此文件，选择"以管理员身份运行"。
echo.
echo 或者使用以下命令一次性安装所有依赖：
echo pip install -r requirements.txt
echo ===================================
echo.

pause 