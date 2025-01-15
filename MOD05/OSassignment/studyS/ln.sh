/bin/rm -rf ln.dir
mkdir ln.dir
cd ln.dir

echo "Hello World" >a
ln a b
ls -li a b
rm a
cat b
ln b a
ls -li a b
ln -s a c
cat c
/bin/rm a b
ls -li c
cat c
echo "Hello World" >a
ls -li a c
cat c
cd ..
