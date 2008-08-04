#!/bin/sh

for f in 5 6 7 8 9 10 11 12 13 14 ; do 

echo "-------------------------------------------------"
echo "cat tree.sc.plf gen${f}.sc.plf | ../../../../sc2/opt/sc --no-tail-calls"
time cat tree.sc.plf gen${f}.sc.plf | ../../../../sc2/opt/sc --no-tail-calls
time cat tree.sc.plf gen${f}.sc.plf | ../../../../sc2/opt/sc --no-tail-calls
time cat tree.sc.plf gen${f}.sc.plf | ../../../../sc2/opt/sc --no-tail-calls

done


