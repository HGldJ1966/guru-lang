CFLAGS=-w -m32 -DDEBUG

all: print-uwarray debug_log debug_log_r sort_example

# special rules

debug_log_r : debug_log.c
	cc -w -m32 -o $@ $<


# general rules

.SUFFIXES: .c .g

%.c: %.g
	../bin/guru $<

%: %.c
	cc $(CFLAGS) -o $@ $<

comb:	
	../bin/guru comb.g

