Include trusted "../lib/stdio.g".
Include "sort.g".

%=============================================================================
% print_ulist
% - f : a function that formats each item
% - g : a function that prints a delimiter
%=============================================================================

Define print_ulist_loop := fun print_ulist_loop
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (^#owned l:<ulist A>)
  : #unique_point stdio_t.
  match l with
    unil _ => % exit loop
      io
  | ucons _ a l' => % print a space and the i'th word, then continue
      let io = (g io) in
      let io = (f io a) in
      (print_ulist_loop io A f g l')
  end.

Define print_owned_ulist := fun
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (^#owned l:<ulist A>)
  : #unique_point stdio_t.
  match l with
    unil _ => % nothing to print
      io
  | ucons _ a l' =>
      % print the first item
      let io = (f io a) in
      
      % print the rest (will be seperated by delimiters)
      (print_ulist_loop io A f g l')
  end.

Define print_ulist := fun
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (^l:<ulist A>)
  : #unique_point stdio_t.
	let io = (print_owned_ulist io A f g (inspect <ulist A> l)) in
  do
  (consume_unowned <ulist A> l)
  io
  end.

Define print_ulist' := fun
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (!l:<ulist A>)
  : #unique_point stdio_t.
	(print_ulist io A f g (inspect <ulist A> l)).


%=============================================================================
% The main function
%=============================================================================

Define print_word :=
  fun(#unique_point io:stdio_t)(w:word) : #unique_point stdio_t.
  (print_string io (word_num_to_string w)).

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
