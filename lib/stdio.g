%Set "print_parsed".

Include trusted "char.g".
Include "pair.g".
Include "unit.g".
Include trusted "string.g".
Include "unique_owned.g".

%Set "print_parsed".

Define primitive stdio_t : type := <pair string string> <<END
  #define gdelete_stdio_t(x) 

  void *curc = 0;

  inline void *gnext_char(void *x) {
    gcur_char2(x); // to make sure we have read a character
    curc = 0;
    return 1;
  }

  inline int gcur_char2(void *s) {
     if (curc == 0) {
	int tmp = fgetc(stdin);
	curc = (tmp == -1 ? 0 : tmp);
     }
     return curc;
  }

END.

Define primitive stdio : #unique_point stdio_t <<END
  #define gstdio 0
END.

Define primitive cur_char2 : Fun(^ #unique_owned_point x:stdio_t). #untracked char :=
  fun(x:stdio_t): char.
    match (fst string string x) with
      unil _ => Cc0
    | ucons _ a l => a
    end
<<END

// C code included above

END.

Define cur_char : Fun(! #unique_point x:stdio_t). #untracked char := 
  fun(! #unique_point x:stdio_t): #untracked char.
    (cur_char2 (inspect_unique_point stdio_t x)).
    

Define primitive next_char := 
  fun(#unique_point x:stdio_t): #unique_point stdio_t.
    match (fst string string x) with
      unil _ => x
    | ucons _ a l => (mkpair string string l (snd string string x))
    end 
<<END
 // C code included above
END.

Define primitive print_char := 
  fun(#unique_point x:stdio_t)(#untracked c:char): #unique_point stdio_t.
     match (eqchar c Cc0) with
       ff => (mkpair string string (fst string string x) (stringc c (snd string string x)))
     | tt => x
     end 
<<END
  int gprint_char(int stdio /* ignore */, int c) {
    if (c == 0)
      return 1;
    fputc(c, stdout);
    return 1;
  }
END.

Define is_eof := fun(c:char).(eqchar c Cc0).

Define print_string : Fun(#unique_point x:stdio_t)(s:string).#unique_point stdio_t :=
  fun print_string(#unique_point x:stdio_t)(s:string):#unique_point stdio_t.
    match s with
      unil _ => x
    | ucons _ c s' => let x' = (print_char x c) in
                        (print_string x' s')
    end.
  
Define println_string : Fun(#unique_point x:stdio_t)(s:string).#unique_point stdio_t :=
  fun(#unique_point x:stdio_t)(s:string):#unique_point stdio_t.
    let x' = (print_string x s) in
    (print_char x' Cnl).

Inductive read_until_char_t : type :=
  return_read_until_char : Fun(s:string)(eof:bool)(#unique_point stdio:stdio_t).#unique read_until_char_t.

% read until we reach character c, and then stop, reading also that occurrence of c iff eat_char is true.
% We also stop if we reach the end of file.
Define read_until_char : Fun(#unique_point stdio:stdio_t)(c:char)(u:{ (eqchar c Cc0) = ff })
                            (eat_char:bool).#unique read_until_char_t :=
  fun r(#unique_point stdio:stdio_t)(c:char)(u:{ (eqchar c Cc0) = ff})(eat_char:bool):#unique read_until_char_t.
    let d = (cur_char stdio) in
    match (eqchar d c) with
      ff => match (eqchar d Cc0) with
              ff => match (r (next_char stdio) c u eat_char) with
                      return_read_until_char s eof stdio => (return_read_until_char (stringc d s) eof stdio)
                    end
            | tt => % end of file
              (return_read_until_char (inc string stringn) tt stdio)
            end
    | tt => (return_read_until_char (inc string stringn) ff match eat_char with ff => stdio | tt => (next_char stdio) end)
    end.


%=============================================================================
% print_word : prints a word (in decimal format)
%=============================================================================

Define print_word_d :=
  fun(#unique_point io:stdio_t)(w:word) : #unique_point stdio_t.
  (print_string io (word_num_to_string w)).

Define print_word := print_word_d.


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
% print_uwarray
% - f : a function that formats each item
% - g : a function that prints a delimiter
%=============================================================================
Include trusted "uwarray.g".

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
