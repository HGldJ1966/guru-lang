go:	wordhist

strange_vec:	
	java -cp .. guru.Main strange_vec.g

pml_proofs:
	java -cp .. guru.Main pml_proofs.g

llambda:
	java -cp .. guru.Main llambda.g

append:
	java -cp .. guru.Main append.g

compiletest:	compiletest.g ../guru/Main.class
	java -cp .. guru.Main compiletest.g
	$(MAKE) c

c:
	gcc -O0 -ggdb -c compiletest.c
	gcc -O0 -ggdb -o compiletest compiletest.o
	./compiletest < compiletest-data

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