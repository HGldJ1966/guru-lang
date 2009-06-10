Include trusted "char.g".
Include "pair.g".
Include "unit.g".
Include trusted "string.g".
Include "unique.g".

Define primitive stdio_t : type := <pair string string> <<END
  #define gstdio_t int
END.

Define primitive stdio : stdio_t := (mkpair string string stringn stringn) <<END
  #define gstdio 0
END.

Define primitive cur_char : Fun(^#unique x:stdio_t).char := 
  fun(^#unique x:stdio_t): char.
    match (fst string string x) with
      unil _ => Cc0
    | ucons _ a l => a
    end
<<END

  void *curc = 0;

  int gcurc(void *s) {
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
  fun(#unique x:stdio_t)(c:char): #unique stdio_t.
    (mkpair string string (fst string string x) (stringc c (snd string string x))) 
<<END
  gchar gprint_char(gchar c) {
    fputc(c, stdout);
  }
END.

