Include "unique.w".
Include "bool.w".
Include "list.w".

Datatype stdin_t with delete_stdin_t : Fun(^x:stdin_t).void <<END
  #define gdelete_stdin_t(x) fclose(x)
END

Datatype char with delete_char : Fun(^c:char).void <<END
  #define gdelete_char(c) 
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

Function read_all(^x:unique).unowned :=
  let c = (curc x) in
  match (eof c) with
    ff => (ucons c (read_all (nextc x)))
  | tt => do (close x) nil end
  end.

Function print_list(^x:owned).void :=
  match x with
    unil => done
  | ucons a x' => do (printc a) (print_list x') end
  end.

