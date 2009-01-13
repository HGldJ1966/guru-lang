#!/bin/sh

for f in 1000 5000 10000 15000 20000 25000 ; do 

echo "-------------------------------------------------"
echo "cat nat.sc2.plf gen${f}.sc2.plf | ../../../../sc2/opt/sc "
time cat nat.sc2.plf gen${f}.sc2.plf | ../../../../sc2/opt/sc
time cat nat.sc2.plf gen${f}.sc2.plf | ../../../../sc2/opt/sc
time cat nat.sc2.plf gen${f}.sc2.plf | ../../../../sc2/opt/sc

done


