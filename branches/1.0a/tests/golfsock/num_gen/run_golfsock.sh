#!/bin/sh

for f in 1000 5000 10000 15000 20000 25000 ; do 

echo "-------------------------------------------------"
echo "cat nat.plf gen${f}.plf | ../golfsock-opt "
time cat nat.plf gen${f}.plf | ../golfsock-opt
time cat nat.plf gen${f}.plf | ../golfsock-opt
time cat nat.plf gen${f}.plf | ../golfsock-opt

done


