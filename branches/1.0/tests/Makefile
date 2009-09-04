test-queue:	test-queue.c
	gcc -O2 -w -o test-queue test-queue.c
	time cat war-and-peace.txt | ./test-queue || echo "problem"

test-queue.c:	test-queue.g ../lib/queue.g Makefile
	../bin/guru test-queue.g

Qp:	test-queue.c
	gcc -O0 -ggdb -p -w -o test-queue-gprof test-queue.c
	time cat war-and-peace.txt | ./test-queue-gprof || echo "problem"

Qd:	test-queue.c
	gcc -O0 -ggdb -w -o test-queue-debug test-queue.c
	time cat war-and-peace.txt | ./test-queue-debug || echo "problem"

test-queue1:	test-queue1.c
	gcc -O2 -w -o test-queue1 test-queue1.c
	time cat war-and-peace.txt | ./test-queue1 || echo "problem"

test-queue1.c:	test-queue1.g Makefile
	../bin/guru test-queue1.g

Q1p:	test-queue1.c
	gcc -O0 -ggdb -p -w -o test-queue1-gprof test-queue1.c
	time cat war-and-peace.txt | ./test-queue1-gprof || echo "problem"

Q1d:	test-queue1.c
	gcc -O0 -ggdb -w -o test-queue1-debug test-queue1.c

test-queuec:	test-queuec.ml Makefile
	ocamlopt test-queuec.ml -o test-queuec

test-queuec1:	test-queuec1.ml Makefile
	ocamlopt test-queuec1.ml -o test-queuec1

test-queue2:	test-queue2.hs Makefile
	ghc -O2 -o test-queue2 --make test-queue2.hs

test-warray1a:	test-warray.g Makefile
	../bin/guru test-warray.g
	gcc -O2 -w -o test-warray1a test-warray.c
	./test-warray1a

test-warray2a:	test-warray2.g Makefile
	../bin/guru test-warray2.g
	gcc -O2 -w -o test-warray2a test-warray2.c
	valgrind ./test-warray2a

test-warray1b:   test-warray.hs Makefile
	ghc -O2 -o test-warray1b --make test-warray.hs

test-warray2b:	test-warray2.hs Makefile
	ghc -O2 -o test-warray2b --make test-warray2.hs

cinv_example: cinv_example.g
	../bin/guru cinv_example.g

test-uwarray:	test-uwarray.g Makefile
	../bin/guru test-uwarray.g
	gcc -O2 -w -o test-uwarray test-uwarray.c
	valgrind ./test-uwarray

test-charray:	test-charray.g Makefile
	../bin/guru test-charray.g
	$(MAKE) test-charray-C

test-qcharray:	test-qcharray.g Makefile
	../bin/guru test-qcharray.g
	gcc -O0 -ggdb -w -o test-qcharray test-qcharray.c
	valgrind ./test-qcharray

test-charray-C:
	gcc -O0 -ggdb -w -o test-charray test-charray.c
	valgrind ./test-charray

test-unique-owned:	test-unique-owned.g Makefile
	../bin/guru test-unique-owned.g
	gcc -O0 -ggdb -w -o test-unique-owned test-unique-owned.c
	valgrind ./test-unique-owned


hello-world:	hello-world.g Makefile
	../bin/guru hello-world.g
	gcc -O0 -ggdb -w -o hello-world hello-world.c
	echo "c" | valgrind ./hello-world
	@echo ""
	@./hello-world 

compiletest:	compiletest.g ../guru/Main.class Makefile
	../bin/guru compiletest.g
	$(MAKE) c

test-stdio:	test-stdio.g
	../bin/guru test-stdio.g
	gcc -O0 -ggdb -w -o test-stdio test-stdio.c
	echo "c" | valgrind ./test-stdio 

c:
	gcc -O0 -ggdb -w -o compiletest compiletest.c
	valgrind ./compiletest 

go:	test_cell

test_cell: test_cell.g
	../bin/guru cell.g test_cell.g

T:	
	gcc -O0 -ggdb -c test_cell.c
	gcc -O0 -ggdb -o test_cell test_cell.o

vec_test:
	java -cp .. guru.Main vec_test.g

strange_vec:	
	java -cp .. guru.Main strange_vec.g

pml_proofs:
	java -cp .. guru.Main pml_proofs.g

llambda:
	java -cp .. guru.Main llambda.g

append:
	java -cp .. guru.Main append.g

foo:	foo.c
	gcc -O0 -ggdb -c foo.c
	gcc -O0 -ggdb -o foo foo.o

b:
	gcc -O0 -ggdb -c bp.c
	gcc -O0 -ggdb -o bp bp.o
Bp:
	gcc -O0 -pg -c bp.c
	gcc -O0 -pg -o bp bp.o

B:
	gcc -O4 -c bp.c
	gcc -O4 -o bp bp.o

bph:	bph.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 bph.hs -o bph

bpc:	bpc.ml
	ocamlopt -unsafe -noassert bpc.ml -o bpc


bp:	bp.g ../lib/stdio.g ../lib/bool.g ../lib/nat.g \
	../guru/Main.class ../guru/compiler/Compiler.class
	java -cp .. guru.Main bp.g
	$(MAKE) B

histh:	histh.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 histh.hs -o histh

histh2:	histh2.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 histh2.hs -o histh2

histc:	histc.ml
	ocamlopt -unsafe -noassert histc.ml -o histc
H:	
	gcc -O4 hist.c -o hist

hist:	hist.g
	java -cp .. guru.Main hist.g
	$(MAKE) H

hist-test1c:	hist-test1c.ml
	ocamlopt -unsafe -noassert hist-test1c.ml -o hist-test1c

hist-test1:	hist-test1.g
	java -cp .. guru.Main hist-test1.g
	gcc -O4 hist-test1.c -o hist-test1

hist-test1h:	hist-test1h.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 hist-test1h.hs -o hist-test1h

hist-test2c:	hist-test2c.ml
	ocamlopt -unsafe -noassert hist-test2c.ml -o hist-test2c

hist-test2:	hist-test2.g
	java -cp .. guru.Main hist-test2.g
	gcc -O4 hist-test2.c -o hist-test2

hist-test2h:	hist-test2h.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 hist-test2h.hs -o hist-test2h


W:	
#	gcc -O0 -pg -ggdb wordhist.c -o wordhist
	gcc -O4 wordhist.c -o wordhist
#	gcc -O0 -ggdb wordhist.c -o wordhist

wordhist:	wordhist.g
	java -cp .. guru.Main wordhist.g
	$(MAKE) W

W1:	
	gcc -O4  wordhist1.c -o wordhist1
#	gcc -O0 -ggdb wordhist1.c -o wordhist1

wordhist1:	wordhist1.g
	java -cp .. guru.Main wordhist1.g
	$(MAKE) W1

W2:	
	gcc -O4  wordhist2.c -o wordhist2
#	gcc -O0 -ggdb wordhist1.c -o wordhist1

wordhist2:	wordhist2.g
	java -cp .. guru.Main wordhist2.g
	$(MAKE) W2

wordhistc-int: wordhistc-int.ml
	ocamlopt -p -unsafe -noassert wordhistc-int.ml -o wordhistc-int

Wc:
	ocamlopt -unsafe -noassert wordhistc.ml -o wordhistc

W1c:	
	ocamlopt -unsafe -noassert wordhist1c.ml -o wordhist1c  

W2c:	
	ocamlopt -unsafe -noassert wordhist2c.ml -o wordhist2c  

# -p for profiling

#histca:	histc.ml
#	ocamlopt -S -unsafe -noassert -c histc.ml

C:	
	gcc -O4 cat.c -o cat

cat:	cat.g
	java -cp .. guru.Main cat.g
	$(MAKE) C

catc:	catc.ml
	ocamlopt -unsafe -noassert catc.ml -o catc

cath:	cath.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 cath.hs -o cath

readh:	readh.hs
	ghc  --make -O2 -fglasgow-exts -fexcess-precision -fasm \
	  -optc-march=pentium4 readh.hs -o readh

R:
	gcc -O4 read.c -o read

read:	read.g
	java -cp .. guru.Main read.g
	$(MAKE) R

readc:	readc.ml
	ocamlopt -unsafe -noassert readc.ml -o readc

read2c:	read2c.ml
	ocamlopt -unsafe -noassert read2c.ml -o read2c

p:
	gcc -O0 -ggdb -c polyfun.c
	gcc -O0 -ggdb -o polyfun polyfun.o

polyfun:	polyfun.g ../lib/stdio.g ../lib/list.g \
	../guru/Main.class
	java -cp .. guru.Main polyfun.g
	$(MAKE) p

xmlcr:	xmlcr.g
	java -cp .. guru.Main xmlcr.g
	$(MAKE) X

X:
	gcc -O0 -ggdb -o xmlcr xmlcr.c
