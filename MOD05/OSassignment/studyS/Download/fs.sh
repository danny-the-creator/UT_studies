gcc Fadvise.c
( sudo ./a.out foo ; times )

sudo fdisk -l
sudo mkdir -p /media/usb
sudo mount /dev/sda1 /media/usb/
( sudo ./a.out /media/usb/foo ; times )
du -sh /media/usb/foo
sudo umount /dev/sda1

sudo mkfs.ext4 /dev/sda1 -L pieter
sudo mount /dev/sda1 /media/usb/
( sudo ./a.out /media/usb/foo ; times )
du -sh /media/usb/foo
sudo umount /dev/sda1
sudo fsck /dev/sda1
