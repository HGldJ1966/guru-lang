%=============================================================================
%- [debug logging]
We would like to print to stderr without any side effects in the
computation for debug purposes. I'm experimenting with some printing
functions, which return type is void. Technically, these loggings are
carraway resource annotations. But, effectively, they can describe
harmless side effects.
Also, it would be handy if we can control whether it really prints or
not using a compiler flag, namely DEBUG. (see Makefile)

- basic functions
log_char, log_string

- naming scheme
"log_" ++ datatype
The ' mark (as in nat') means that the argument is NOT consumed.
By default, the input arguments are consumed. But, sometimes, we don't want
that behavior.

- notes
Even if we can control printing, the printing code is still generated.
But, unfortunately, I don't know how to completely eliminate the
unnecessary computation when we decided not to print.
-%
%=============================================================================
Include trusted "../lib/char.g".
Include trusted "../lib/string.g".
Include trusted "../lib/nat.g".

% noop is needed because voidi itself would NOT compile
Define primitive noop := voidi <<END
  #define gnoop
END.

Define primitive log_char := fun(#untracked c:char). voidi <<END
  void do_log_char(unsigned c) {
    fputc(c, stderr);
    if (c == '\n')
      fflush( stderr );	// automatic flushing inspired by clog in C++
  }
  #ifdef DEBUG
  #define glog_char( c )		do_log_char( c )
  #else
  #define glog_char( c )
  #endif
END.

Define log_owned_string := fun log_owned_string(^#owned s:string) : void.
	match s with
		unil _ => noop
	| ucons _ c s' =>
			do (log_char c)
				 (log_owned_string s')
			end
	end.

Define log_string := fun(^s:string) : void.
	do
	(log_owned_string (inspect string s))
	(consume_unowned string s)
	end.

Define log_string' := fun(!s:string) : void.
	(log_owned_string (inspect string s)).
