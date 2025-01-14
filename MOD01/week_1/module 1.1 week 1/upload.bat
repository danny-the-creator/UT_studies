@ECHO OFF

IF "%1"=="help" GOTO helpmenu
IF "%1"=="" GOTO helpmenu
IF "%2"=="" GOTO helpmenu

ECHO -- Converting to hex....

files\hex2hex.exe  < %2 > files/intel.hex
IF %errorlevel% NEQ 0 GOTO error

ECHO -- Uploading...
avrdude-7.2\bin\avrdude -q -q -patmega328p -carduino -P %1 -b115200 -D -Uflash:w:files/intel.hex:i
IF %errorlevel% NEQ 0 GOTO error

echo -- OK!
GOTO end

:error
ECHO -- Aborted due to error (level %errorlevel%).
exit /b  %errorlevel%
PAUSE

:helpmenu
ECHO Usage: upload port filename
PAUSE

:end
