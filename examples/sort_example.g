Include trusted "../lib/stdio.g".
Include "sort.g".

%=============================================================================
% The main function
%=============================================================================

Define print_space := fun
  fun(#unique_point io:stdio_t) : #unique_point stdio_t.
  (print_char io ' ').

Define sample_list :=
  % some random values
  (ucons word 0x3
	(ucons word 0x1
	(ucons word 0x5
	(ucons word 0x2
	(ucons word 0x4
		(unil word)))))).

Define main :=
  abbrev l = sample_list in
  let l' = (usort word ltword (inspect <ulist word> l)) in

  let stdio = (print_ulist stdio word print_word print_space l) in
  let stdio = (print_char stdio '\n') in

  let stdio = (print_ulist stdio word print_word print_space l') in
  let stdio = (print_char stdio '\n') in
  
  (consume_unique_point stdio_t stdio)
  .

Compile main to "sort_example.c".
