/bin/rm -rf /tmp/db /tmp/submit
mkdir /tmp/db
chmod 700 /tmp/db
gcc '-DDIR="/tmp/db/"' -Wall -pedantic Setuid.c
mv a.out /tmp/submit
chmod +s /tmp/submit
echo "aap" | /tmp/submit
ls -lR /tmp/db /tmp/submit
