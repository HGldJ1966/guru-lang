#!/bin/sh

ulimit -t 1800

for f in mini cnt01e tree-exa2-10 cnt01re toilet_a_02_01.2 1qbf-5cnf-20var-160cl.0 1qbf-5cnf-20var-160cl.1 tree-exa2-15 toilet_a_02_01.3 ; do 

echo "-------------------------------------------------"

echo "cat logic.plf bench/${f}.golfsock.plf | ../golfsock-opt"
time cat logic.plf bench/${f}.golfsock.plf | ../golfsock-opt
time cat logic.plf bench/${f}.golfsock.plf | ../golfsock-opt
time cat logic.plf bench/${f}.golfsock.plf | ../golfsock-opt

done
