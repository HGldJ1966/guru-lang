Include trusted "char.g".
Include "ulist.g".

Define string := <ulist char>.
Define stringn := (unil char).
Define stringc := (ucons char).
Define string_app := fun(s1 s2:string).
                      let ret = (uappend char s1 s2) in do (dec string s1) ret end.
Define string_appnl := fun(s1:string)(s2:string).
                         (string_app (stringc Cnl s1) s2).
Define stringeq := (equlist char eqchar).

Define stringeqEq : Forall(s1 s2:string)(u: {(stringeq s1 s2) = tt}).
                      { s1 = s2 } :=
  foralli(s1 s2:string).
    [equlistEq char s1 s2 eqchar eqchar_tot eqchar_eq].

Define stringeqTot := 
  foralli(s1 s2:string).[equlist_total char eqchar eqchar_tot s1 s2].

