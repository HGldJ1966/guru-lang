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

Define primitive stdio : Fun(#untracked u:Unit).#unique stdio_t <<END
  #define gstdio(x) 0
END.

Define primitive cur_char : Fun(! #unique x:stdio_t). #untracked char := 
  fun(x:stdio_t): char.
    match (fst string string x) with
      unil _ => Cc0
    | ucons _ a l => a
    end
<<END

  void *curc = 0;

  int gcur_char(void *s) {
     if (curc == 0) {
	int tmp = fgetc(stdin);
	curc = (tmp == -1 ? 0 : tmp);
     }
     return curc;
  }

END.

Define primitive next_char := 
  fun(#unique x:stdio_t): #unique stdio_t.
    match (fst string string x) with
      unil _ => x
    | ucons _ a l => (mkpair string string l (snd string string x))
    end 
<<END

  void *gnextc(void *x) {
    curc = 0;
    return x;
  }

END.

Define primitive print_char := 
  fun(#unique x:stdio_t)(#untracked c:char): #unique stdio_t.
    (mkpair string string (fst string string x) (stringc c (snd string string x))) 
<<END
  int gprint_char(int stdio /* ignore */, int c) {
    fputc(c, stdout);
  }
END.

Define print_string : Fun(#unique x:stdio_t)(s:string).#unique stdio_t :=
  fun print_string(#unique x:stdio_t)(s:string):#unique stdio_t.
    match s with
      unil _ => x
    | ucons _ c s' => let x' = (print_char x c) in
                        (print_string x' s')
    end.
  
Define println_string : Fun(#unique x:stdio_t)(s:string).#unique stdio_t :=
  fun(#unique x:stdio_t)(s:string):#unique stdio_t.
    let x' = (print_string x s) in
    (print_char x' Cnl).
