CFLAGS=-w -m32 -DDEBUG

all: print-uwarray debug_log.c debug_log

# general rules

.SUFFIXES: .c .g .

%.c: %.g
	guru $<

%: %.c
	cc $(CFLAGS) -o $@ $<
