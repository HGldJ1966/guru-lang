Include trusted "../lib/uwarray.g".
Include trusted "../lib/stdio.g".

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
