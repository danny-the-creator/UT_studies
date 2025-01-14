@ECHO OFF

IF "%1"=="help" GOTO helpmenu
IF "%1"=="" GOTO helpmenu
IF "%2"=="" GOTO helpmenu

ECHO -- Converting to hex....

"avra-1.4.2/bin/avra" %2 -o files\intel.hex -e files\intel.eep.hex -d files\intel.obj
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
ECHO Usage: asmupload port filename
PAUSE

:end
