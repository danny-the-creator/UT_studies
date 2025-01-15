/bin/rm -rf fadvise.dir
mkdir fadvise.dir
cd fadvise.dir

gcc ../Fadvise.c
/bin/rm -rf Foo Foo1 Bar Bar1
free -m
time ./a.out Foo
free -m
time cp Foo Foo1
free -m
time ./a.out Bar x
free -m
time cp Bar Bar1
free -m
ls -lh Foo* Bar*
/bin/rm -rf Foo Foo1 Bar Bar1 a.out
cd ..
