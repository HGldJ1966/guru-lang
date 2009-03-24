Include "unique.w".

Datatype stdin_t with gdelete_stdin_t : Fun(^x:stdin_t).void <<END
  void gdelete_stdin_t(void *x) {}
END

Datatype char with gdelete_char : Fun(^c:char).void <<END
  void gdelete_char(void *c) {}
END

Primitive stdin : unique <<END
  #include <stdio.h>

  #define gstdin stdin
END

Primitive curc : Fun(!x:unique).untracked <<END

  void *curc = 0;

  int gcurc(void *s) {
     if (curc == 0) {
	int tmp = fgetc((FILE *)s);
	curc = (tmp == -1 ? 0 : tmp);
     }
     return curc;
  }
END

Primitive nextc : Fun(^x:unique).unique <<END
  void *gnextc(void *x) {
    curc = 0;
    return x;
  }
END

Primitive eof : Fun(c:untracked).untracked <<END
  int geof(int x) {
    return x == 0;
  }
END

Primitive printc : Fun(c:untracked).void <<END
  void gprintc(int c) {
    putchar(c);
    fflush(stdout);
  }
END

Primitive close : Fun(^x:unique).void <<END
  void gclose(void *s) {
    fclose(s);
  }
END

