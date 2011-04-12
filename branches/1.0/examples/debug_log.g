%=============================================================================
% example
%=============================================================================
Include "../lib/stdio.g".
Include "../lib/debug_log.g".

Define sum := fun sum(n:nat) : nat.
  match !n with
  	Z =>
  		do
  		(consume_unowned nat n)
  		Z
  		end
  | S n' =>
  		do
  		(log_string (string_app1 (natToString' n) (inc string stringln)))
  		(plus n (sum n'))
  		end
  end.
  
Define main :=
	let	v = (sum five) in
	do
	(log_string "---\n" )
	let v' = (inc_word_by_nat word0 (inspect nat v)) in
	let stdio = (print_string stdio (word_num_to_string v')) in
	let stdio = (print_char stdio '\n') in
	do
	(consume_unowned nat v)
	(consume_unique_point stdio_t stdio)
	end
	end.

Compile main to "debug_log.c".
