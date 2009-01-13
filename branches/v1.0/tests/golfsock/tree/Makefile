all: gen
	./gen 5 > gen5.plf
	./gen 6 > gen6.plf
	./gen 7 > gen7.plf
	./gen 8 > gen8.plf
	./gen 9 > gen9.plf
	./gen 10 > gen10.plf
	./gen 11 > gen11.plf
	./gen 12 > gen12.plf
	./gen 13 > gen13.plf
	./gen 14 > gen14.plf
	./gen -s 5 > gen5.sc.plf
	./gen -s 6 > gen6.sc.plf
	./gen -s 7 > gen7.sc.plf
	./gen -s 8 > gen8.sc.plf
	./gen -s 9 > gen9.sc.plf
	./gen -s 10 > gen10.sc.plf
	./gen -s 11 > gen11.sc.plf
	./gen -s 12 > gen12.sc.plf
	./gen -s 13 > gen13.sc.plf
	./gen -s 14 > gen14.sc.plf
	./gen -t 5 > gen5.elf
	./gen -t 6 > gen6.elf
	./gen -t 7 > gen7.elf
	./gen -t 8 > gen8.elf
	./gen -t 9 > gen9.elf
	./gen -t 10 > gen10.elf
	./gen -t 11 > gen11.elf
	./gen -t 12 > gen12.elf
	./gen -t 13 > gen13.elf
	./gen -t 14 > gen14.elf

gen -t: gen.c
	gcc -o gen gen.c

