GHC=ghc-6.10.4
#GCC=/usr/mygcc/bin/gcc

test_queue_g:	test_queue_g.c
	$(GCC) -O2 -w -o test_queue_g test_queue_g.c

test_queue_gd:	test_queue_g.c
	$(GCC) -O0 -w -ggdb -o test_queue_gd test_queue_g.c

test_queue_g.c:	test_queue_g.g
	../../../bin/guru test_queue_g.g

test_queue_c:	test_queue_c.ml 
	ocamlopt test_queue_c.ml -o test_queue_c

test_queue_h:	test_queue_h.hs 
	$(GHC) -O2 -o test_queue_h --make test_queue_h.hs

test_warray_g:	test_warray_g.g 
	../../../bin/guru test_warray_g.g
	$(GCC) -O2 -w -o test_warray_g test_warray_g.c

test_warray_gp:	test_warray_g.g 
	../../../bin/guru test_warray_g.g
	$(GCC) -O2 -w -pg -o test_warray_gp test_warray_g.c

test_warray_h:   test_warray_h.hs 
	$(GHC) -O2 -o test_warray_h --make test_warray_h.hs

test_warray_c:   test_warray_c.ml 
	ocamlopt -o test_warray_c test_warray_c.ml

test_warray_cp:   test_warray_c.ml 
	ocamlopt -o test_warray_cp -p test_warray_c.ml

clean:
	rm -f test_warray_h test_warray_c test_warray_g test_queue_h test_queue_c test_queue_g test_warray_g.c test_queue_g.c
	rm -f test_warray_hp test_warray_cp test_warray_gp test_queue_hp test_queue_cp test_queue_gp 
	rm -f *.cmi *.cmx *.o *.hi

test_warray: test_warray_h test_warray_c test_warray_g

test_queue: test_queue_h test_queue_c test_queue_g 

run_warray: test_warray
	@echo "----------------------------"
	@echo "Haskell warray"
	@echo ""
	time ./test_warray_h
	time ./test_warray_h
	time ./test_warray_h
	@echo "----------------------------"
	@echo "OCaml warray"
	@echo ""
	time ./test_warray_c
	time ./test_warray_c
	time ./test_warray_c
	@echo "----------------------------"
	@echo "Guru warray"
	@echo ""
	time ./test_warray_g
	time ./test_warray_g
	time ./test_warray_g
	@echo "----------------------------"

run_queue: test_queue
	@echo "----------------------------"
	@echo "Haskell queue"
	@echo ""
	time ./test_queue_h < war-and-peace.txt
	time ./test_queue_h < war-and-peace.txt
	time ./test_queue_h < war-and-peace.txt
	@echo "----------------------------"
	@echo "OCaml queue"
	@echo ""
	time ./test_queue_c < war-and-peace.txt
	time ./test_queue_c < war-and-peace.txt
	time ./test_queue_c < war-and-peace.txt
	@echo "----------------------------"
	@echo "Guru queue"
	@echo ""
	time ./test_queue_g < war-and-peace.txt
	time ./test_queue_g < war-and-peace.txt
	time ./test_queue_g < war-and-peace.txt
	@echo "----------------------------"

run_extra:	test_warray test_queue
	@echo "-----------------------------"
	@echo "Haskell warray no GC"
	@echo ""
	time ./test_warray_h +RTS -A500m -H500m -smyout.txt -RTS
	time ./test_warray_h +RTS -A500m -H500m -smyout.txt -RTS
	time ./test_warray_h +RTS -A500m -H500m -smyout.txt -RTS
	@echo "-----------------------------"
	@echo "Haskell queue no GC"
	@echo ""
	time ./test_queue_h +RTS -A500m -H500m -smyout.txt -RTS < war-and-peace.txt
	time ./test_queue_h +RTS -A500m -H500m -smyout.txt -RTS < war-and-peace.txt
	time ./test_queue_h +RTS -A500m -H500m -smyout.txt -RTS < war-and-peace.txt
	@echo "-----------------------------"
	@echo "OCaml warray no GC"
	@echo ""
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_warray_c
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_warray_c
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_warray_c
	@echo "----------------------------"
	@echo "OCaml queue no GC"
	@echo ""
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_queue_c < war-and-peace.txt
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_queue_c < war-and-peace.txt
	export OCAMLRUNPARAM 's=500M,h=500M,v=0x1ff'; time ./test_queue_c < war-and-peace.txt
	@echo "----------------------------"

run:	run_warray run_queue
run2:	run run_extra

