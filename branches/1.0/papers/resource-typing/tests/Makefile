test-queue-g:	test-queue-g.c
	gcc -O2 -w -o test-queue-g test-queue-g.c
	time ./test-queue-g < war-and-peace.txt || echo "problem"

test-queue-g.c:	test-queue-g.g
	../../../bin/guru test-queue-g.g

test-queue-c:	test-queue-c.ml Makefile
	ocamlopt test-queue-c.ml -o test-queue-c

test-queue-h:	test-queue-h.hs Makefile
	ghc -O2 -o test-queue-h --make test-queue-h.hs

test-warray-g:	test-warray-g.g Makefile
	../bin/guru test-warray-g.g
	gcc -O2 -w -o test-warray-g test-warray-g.c
	./test-warray-g

test-warray-h:   test-warray-h.hs Makefile
	ghc -O2 -o test-warray-h --make test-warray-h.hs
