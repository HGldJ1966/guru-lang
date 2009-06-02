#!/bin/sh

for f in 5 6 7 8 9 10 11 12 13 14 ; do 

echo "-------------------------------------------------"
echo "~/research/sc/examples/twelf.sh tree.elf gen${f}.elf"
~/research/sc/examples/twelf.sh tree.elf gen${f}.elf
~/research/sc/examples/twelf.sh tree.elf gen${f}.elf
~/research/sc/examples/twelf.sh tree.elf gen${f}.elf

done


