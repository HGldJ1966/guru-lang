Include "../lib/unit.g".
Include "../lib/stdio.g".

Define read :=
  fun read(unique stdin:stdin_t)(c:char):char.
    match (next_char stdin) with
      getc_none stdin' => dec stdin' c
    | getc_char a stdin' => (read stdin' a)
    end.

Define main :=
  fun(unique stdin:stdin_t).
    let ign = (print_char (read stdin Cnl)) in Z.
 
Compile main to "read.c".
