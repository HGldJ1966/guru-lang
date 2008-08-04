all: gen
	./gen 3 > gen3.plf
	./gen 1000 > gen1000.plf
	./gen 5000 > gen5000.plf
	./gen 10000 > gen10000.plf
	./gen 15000 > gen15000.plf
	./gen 20000 > gen20000.plf
	./gen 25000 > gen25000.plf
	./gen -s 3 > gen3.sc2.plf
	./gen -s 1000 > gen1000.sc2.plf
	./gen -s 5000 > gen5000.sc2.plf
	./gen -s 10000 > gen10000.sc2.plf
	./gen -s 15000 > gen15000.sc2.plf
	./gen -s 20000 > gen20000.sc2.plf
	./gen -s 25000 > gen25000.sc2.plf


gen -s: gen.c
	gcc -o gen gen.c

