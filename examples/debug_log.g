%=============================================================================
%- [debug logging]
we would like to print to stderr without any side effects in the
computation for debug purposes so, here's experimenting some printing
functions, which return type is void. Effectively, these loggings are
carraway resource annotations.
And it would also be handy, we can control whether it really prints or
not using a compiler flag, namely DEBUG. (see Makefile)

- basic functions
log_char, log_string
log_word_d : format word in decimal
log_nat : prints a nat in decimal
log_nat' : prints a nat in decimal (this version does not consume it)

- naming scheme
"log_" ++ datatype ++ formatting option
The ' mark (as in nat') means that the argument is not consumed.
Usually, the input arguments are consumed. But, sometimes, we don't want
that behavior.

- notes
Even if we can control printing, the printing code is still generated.
But, unfortunately, I don't know how to completely eliminate the
unnecessary computation when we decided not to print.
-%

%=============================================================================
% logging
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

Define log_string := fun log_string(^s:string) : void.
	match s with
		unil _ => noop
	| ucons _ c s' =>
			do (log_char c)
				 (log_string s')
			end
	end.

Define log_word_d := fun(w:word) : void.
  (log_string (word_num_to_string w)).

Define inc_word_by_nat := fun inc_word_by_nat(w:word)(^#owned n:nat) : word.
	match n with
		Z => w
	| S n' =>
			let w' = (word_inc2 w) in
			(inc_word_by_nat w' n')
	end.

Define log_nat := fun(^n:nat) : void.
	let w = (inc_word_by_nat word0 (inspect nat n)) in
	do
	(consume_unowned nat n)
	(log_word_d w)
	end.

Define log_nat' := fun(!n:nat) : void.
	let w = (inc_word_by_nat word0 (inspect nat n)) in
	(log_word_d w).


%=============================================================================
% example
%=============================================================================

Define sum := fun sum(n:nat) : nat.
  match !n with
  	Z =>
  		do
  		(consume_unowned nat n)
  		Z
  		end
  | S n' =>
  		do
  		(log_nat' n)
  		(log_char '\n')
  		(plus n (sum n'))
  		end
  end.
  
Define main :=
	(sum three).

Compile main to "debug_log.c".
