Include trusted "../lib/uwarray.g".
Include trusted "../lib/stdio.g".

%=============================================================================
% print_uwarray
% - f : a function that formats each item
% - g : a function that prints a delimiter
%=============================================================================

Define print_uwarray_loop := fun print_uwarray_loop
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (n:word)(^#unique_owned a:<uwarray A n>)
  (i:word)
  : #unique_point stdio_t.
  match (ltword i n) by q1 _ with
    ff => % exit loop
      io
  | tt => % print a space and the i'th word, then continue
      let io = (g io) in
      
      let v = (uwarray_get A n a i q1) in
      let io = (f io v) in
      
      abbrev p1 = [ltword_implies_ltword_word_max i n q1] in
      let i' = (word_inc_safe i p1) in
      (print_uwarray_loop io A f g n a i')
  end.

Define print_uwarray := fun
  (#unique_point io:stdio_t)
  (A:type)
  (f:Fun(#unique_point io:stdio_t)(#untracked a:A).#unique_point stdio_t)
  (g:Fun(#unique_point io:stdio_t).#unique_point stdio_t)
  (n:word)(!#unique a:<uwarray A n>)
  : #unique_point stdio_t.
  match (ltword 0x0 n) by q1 _ with
    ff => % nothing to print
      io

  | tt =>
      let a_i = (inspect_unique <uwarray A n> a) in

      % print the first item
      let v = (uwarray_get A n a_i 0x0 q1) in
      let io = (f io v) in
      
      % print the rest (will be seperated by delimiters)
      (print_uwarray_loop io A f g n a_i 0x1)
  end.


%=============================================================================
% print_word : prints a word (in decimal format)
%=============================================================================

Define print_word :=
  fun(#unique_point io:stdio_t)(w:word) : #unique_point stdio_t.
  (print_string io (word_num_to_string w)).


%=============================================================================
% The main function
%=============================================================================

% a little helper function
Define _set_val := fun
  (n:word)(#unique a:<uwarray word n>)
  (i:word)(w:word)
  :#unique <uwarray word n>.
  % [assert] (ltword i n)
  match (ltword i n) by q1 _ with ff => abort <uwarray word n> | tt =>
  (uwarray_set word n a i w q1)
  end.
  
Define print_space := fun
  fun(#unique_point io:stdio_t) : #unique_point stdio_t.
  (print_char io ' ').

Define sample_array_len := 0x5.
Define sample_array :=
  abbrev len = sample_array_len in
  
  % create an array (initialized with zeros)
  let a = (uwarray_new word len 0x0) in
  
  % set some random values
  %                       idx val
  % ----------------------------------------------------------------
  let a = (_set_val len a 0x0 0x3) in
  let a = (_set_val len a 0x1 0x1) in
  let a = (_set_val len a 0x2 0x5) in
  let a = (_set_val len a 0x3 0x2) in
  let a = (_set_val len a 0x4 0x4) in
  a.

Define main :=
  abbrev len = sample_array_len in
  abbrev a = sample_array in

  let stdio = (print_uwarray stdio word print_word print_space len a) in
  let stdio = (print_char stdio '\n') in
  do
  (consume_unique <uwarray word sample_array_len> a)
  (consume_unique_point stdio_t stdio)
  end.

Compile main to "print-uwarray.c".
