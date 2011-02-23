CFLAGS=-w -m32 -DDEBUG

all: print-uwarray debug_log.c debug_log debug_log_r

debug_log_r : debug_log.c
	cc -w -m32 -o $@ $<

# general rules

.SUFFIXES: .c .g .

%.c: %.g
	guru $<

%: %.c
	cc $(CFLAGS) -o $@ $<
