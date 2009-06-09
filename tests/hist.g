Include "../lib/charvec.g".
Include "../lib/stdio.g".

Set "Debug_compiler".

Define hist := <vec nat num_chars>.
Define mk_hist := (mk_charvec nat).
Define histget := (cvget nat).
Define histupdate := (cvupdate nat).

Opaque hist.
Stub mk_hist.
Stub histget.
Stub histupdate.

Define do_hist :=
  fun hist(unique stdin:stdin_t)(unique h:hist):unique hist.
    match (next_char stdin) with
      getc_none => h
    | getc_char a stdin' =>
        (hist stdin' (histupdate h a (S (histget h a))))
    end.

Define main :=
  fun(unique stdin:stdin_t).
    let ign = (do_hist stdin (mk_hist Z)) in Z.
 
%Compile main to "hist.c".
