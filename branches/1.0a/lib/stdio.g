Include trusted "char.g".
Include "pair.g".
Include "unit.g".
Include trusted "string.g".

Define spec stdio_t := <pair string string>.

Define spec cur_char := 
  fun(unique_owned x:stdio_t): char.
    match (fst string string x) with
      nil A => Cc0
    | cons A a l => a
    end.

Define spec next_char := 
  fun(unique x:stdio_t): unique stdio_t.
    match (fst string string x) with
      nil A => x
    | cons A a l => (mkpair string string l (snd string string x))
    end.

Define spec print_char := 
  fun(unique x:stdio_t)(c:char): unique stdio_t.
    (mkpair string string (fst string string x) (stringc c (snd string string x))).

%-
Define print_nat :=
  fun print_nat(owned n:nat):Unit.
    match n with
      Z => (print_char CZ)
    | S n' => let ign = (print_char CS) in (print_nat n')
    end.

Define print_nat_unique :=
  fun print_nat_unique(unique_owned n:nat):Unit.
    match n with
      Z => (print_char CZ)
    | S n' => let ign = (print_char CS) in (print_nat_unique n')
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
-%