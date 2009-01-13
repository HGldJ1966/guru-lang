#!/bin/sh

for f in 5 6 7 8 9 10 11 12 13 14 ; do 

echo "-------------------------------------------------"
echo "cat tree.plf gen${f}.plf | ../golfsock-opt "
time cat tree.plf gen${f}.plf | ../golfsock-opt
time cat tree.plf gen${f}.plf | ../golfsock-opt
time cat tree.plf gen${f}.plf | ../golfsock-opt

done


