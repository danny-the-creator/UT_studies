/bin/rm -rf sparse.dir
mkdir sparse.dir
cd sparse.dir
gcc ../Sparse.c

for d
in . /tmp
do
	for i
	in 1 2 4 8 16 32 64 128 256 512 1024
	do
		echo "Now in pass $i in $d"
		/bin/rm -rf $d/$i.dat
		time  ./a.out $d/$i.dat $i 
		time cat $d/$i.dat > $d/junk
		ls -l $d/$i.dat $d/junk
		du  $d/$i.dat $d/junk
		/bin/rm -rf $d/$i.dat
	done
done
cd ..
