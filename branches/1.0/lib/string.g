Include "char.g".
Include "list2.g".

Define string := <list char>.
Define stringn := (nil char).
Define stringc := (cons char).
Define string_app := fun(s1 s2:string).
                      let ret = (append char s1 s2) in dec s1 ret.
Define string_appnl := fun(s1:string)(s2:string).
                         (string_app (stringc Cnl s1) s2).
Define stringeq := (eqlist char eqchar).

Define stringeqEq : Forall(s1 s2:string)(u: {(stringeq s1 s2) = tt}).
                      { s1 = s2 } :=
  foralli(s1 s2:string).
    [eqlistEq char s1 s2 eqchar eqchar_tot eqchar_eq].

Define stringeqTot := 
  foralli(s1 s2:string).[eqlist_total char eqchar eqchar_tot s1 s2].

Define bv_to_string :=
  fun bv_to_string(spec l:nat)(c:<bv l>):string.
    match c with
      vecn ign => "b"
    | vecc ign l' b c' =>
      (cons char match b with ff => C0 | tt => C1 end
        (bv_to_string l' c'))
    end.