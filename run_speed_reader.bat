@echo off
REM Enable local script execution just in case (though we use call/bat here)
powershell -Command "Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass"

echo Activating Virtual Environment...
call Scripts\activate.bat

echo Running Speed Reader...
python speed_reader.py

if %ERRORLEVEL% NEQ 0 (
    echo.
    echo Application exited with error code %ERRORLEVEL%.
    pause
)
