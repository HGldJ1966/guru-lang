golfsock:	trm.g symbols.g golfsock.g gs_io.g check.g\
		 deriv.g ../../lib/stdio.g deriv_thm.g var.g symbols_thm.g
		time java -cp ../../src guru.Main golfsock.g
		$(MAKE) G

G:
	gcc -O0 -ggdb -o golfsock golfsock.c

Go:
	gcc -O4 -o golfsock-opt golfsock.c

Gp:
	gcc -O4 -pg -o golfsock-gprof golfsock.c