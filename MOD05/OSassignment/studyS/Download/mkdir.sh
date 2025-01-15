/bin/rm -rf Foo* a.out
mkdir Foo
cd Foo
gcc ../Mkdir.c
for i
in 1 2 4 8 16 32 64 128 256 512 1024 2048 4096
do
        ( ./a.out $i ; times )
        ( /bin/rm -rf Foo* ; times )
done
