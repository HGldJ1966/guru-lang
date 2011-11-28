Include "../lib/unit.g".
Include "../lib/stdio.g".

Define cat :=
  fun cat(unique stdin:stdin_t):Unit.
    match (next_char stdin) with
      getc_none => unit
    | getc_char a stdin' =>
        let ign = (print_char a) in (cat stdin')
    end.

Define main :=
  fun(unique stdin:stdin_t).
    let ign = (cat stdin) in Z.
 
Compile main to "cat.c".
