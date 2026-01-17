@echo off
REM Windows batch wrapper for build script
REM Requires Cygwin or WSL to be installed

echo === TheoryTask Build Wrapper ===
echo.
echo This script will guide you through the build process.
echo.

REM Check if Cygwin is available
where cygwin >nul 2>&1
if %errorlevel% equ 0 (
    echo Detected Cygwin, launching build script...
    cygwin bash build.sh %*
    goto :end
)

REM Check if WSL is available
where wsl >nul 2>&1
if %errorlevel% equ 0 (
    echo Detected WSL, launching build script...
    wsl bash build.sh %*
    goto :end
)

REM Fall back to PowerShell script
echo Neither Cygwin nor WSL detected.
echo Running PowerShell setup script (manual steps required for verification file generation)...
echo.
powershell -ExecutionPolicy Bypass -File build.ps1 %*

:end
echo.
pause
