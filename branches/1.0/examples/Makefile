CFLAGS=-w -m32

all: print-uwarray

print-array: print-uwarray.c
	cc $(CFLAGS) -o $@ $<

.SUFFIXES: .c .g

.g.c:
	guru $<
