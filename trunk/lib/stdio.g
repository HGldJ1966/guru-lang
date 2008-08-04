Include "char.g".
Include "pair.g".
Include "unit.g".
Include "string.g".

Define spec stdin_t := string.

Inductive getc_t : Fun(A:type).type :=
  getc_none : Fun(A:type)(unique l:A).<getc_t A>
| getc_char : Fun(A:type)(a:char)(unique l:A).<getc_t A>.

Define spec next_char := 
  fun(unique x:stdin_t): unique <getc_t stdin_t>.
    match x by u v with
      nil A => (getc_none stdin_t stringn)
    | cons A a l => (getc_char stdin_t a l)
    end.

Define print_nat :=
  fun print_nat(owned n:nat):Unit.
    match n with
      Z => (print_char CZ)
    | S n' => let ign = (print_char CS) in (print_nat n')
    end.

Define nat_to_string :=
  fun nat_to_string(owned n:nat):string.
    match n with
      Z => (stringc CZ inc stringn)
    | S n' => (stringc CS (nat_to_string n'))
    end.

Define print_string :=
  fun print_string(s:string):Unit.
    match s with
      nil A => unit
    | cons A a s' => 
      abbrev P = symm inj <list *> s_Eq in
      let ign = (print_char cast a by P) in
        (print_string cast s' by cong <list *> P)
    end.

Define println_string := 
  fun(s:string).
    let ign = (print_string s) in
      (print_char Cnl).