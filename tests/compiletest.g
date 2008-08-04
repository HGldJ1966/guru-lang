Include "../lib/stdio.g".
Include "../lib/plus.g".

Set "Debug_compiler".

Define foo := (plus Z (S Z)).

Define helper :=
  fun helper(unique l:stdin_t):nat.
    match (next_char l) with
      getc_none => Z
    | getc_char a l => (S (helper l))
    end.

Define print_nat :=
  fun print_nat(n:nat):bool.
    match n with
      Z => let ign = (print_char cZ) in tt
    | S n' => let ign = (print_char cS) in (print_nat n')
    end.

Define my_main := 
  fun(unique l:stdin_t). 
    let ign = (print_nat (helper l)) in
    let ign = (print_char cnl) in
        Z.
	
Compile my_main to "compiletest.c".
