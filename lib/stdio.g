%Set "print_parsed".

Include trusted "char.g".
Include "pair.g".
Include "unit.g".
Include trusted "string.g".
Include "unique.g".

%Set "print_parsed".

Define primitive stdio_t : type := <pair string string> <<END
  #define gdelete_stdio_t(x) 
END.

Define primitive stdio : #unique_point stdio_t <<END
  #define gstdio 0
END.

Define primitive cur_char : Fun(! #unique_point x:stdio_t). #untracked char := 
  fun(x:stdio_t): char.
    match (fst string string x) with
      unil _ => Cc0
    | ucons _ a l => a
    end
<<END

  void *curc = 0;

  inline int gcur_char(void *s) {
     if (curc == 0) {
	int tmp = fgetc(stdin);
	curc = (tmp == -1 ? 0 : tmp);
     }
     return curc;
  }

END.

Define primitive next_char := 
  fun(#unique_point x:stdio_t): #unique_point stdio_t.
    match (fst string string x) with
      unil _ => x
    | ucons _ a l => (mkpair string string l (snd string string x))
    end 
<<END

  inline void *gnext_char(void *x) {
    curc = 0;
    return 1;
  }

END.

Define primitive print_char := 
  fun(#unique_point x:stdio_t)(#untracked c:char): #unique_point stdio_t.
    (mkpair string string (fst string string x) (stringc c (snd string string x))) 
<<END
  int gprint_char(int stdio /* ignore */, int c) {
    fputc(c, stdout);
  }
END.

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
