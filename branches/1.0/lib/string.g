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

Define string_mem := (ulist_mem char eqchar).

Define stringeqEq : Forall(s1 s2:string)(u: {(stringeq s1 s2) = tt}).
                      { s1 = s2 } :=
  foralli(s1 s2:string).
    [equlistEq char s1 s2 eqchar eqchar_tot eqchar_eq].

Define stringeqTot := 
  foralli(s1 s2:string).[equlist_total char eqchar eqchar_tot s1 s2].

Define char_range
 : Fun(c1 c2 : char)(u : { (le (which_char c1) (which_char c2)) = tt }). string :=
fun char_range(c1 c2 : char)(u : { (le (which_char c1) (which_char c2)) = tt }): <ulist char>.
  match (eqchar c1 c2) by v ign with
    ff => abbrev c1_lt_c2 = [eqnat_ff_implies_lt (which_char c1) (which_char c2) 
                              [to_nat_neq1 charlen c1 c2 v] u] in
          abbrev c1_lt_CLast = [ltle_trans (which_char c1) (which_char c2) (which_char CLast)
                                 c1_lt_c2 [chars_bounded2 c2]] in
          (stringc c1 (char_range (char_inc1 c1 c1_lt_CLast) c2
                            trans cong (le * (which_char c2)) [char_inc1_lem c1 c1_lt_CLast]
                                 [lt_S_le (which_char c1) (which_char c2) c1_lt_c2]))
  | tt => stringn
  end.

Define trusted char_range_member
   : Forall (c1 d c2:char)(u:{(le (which_char c1) (which_char c2)) = tt})
            (u1 : { (le c1 d) = tt })(u2: {(le d c2) = tt}).
       { (string_mem d (char_range c1 c2)) = tt } := truei.

Define all_chars := (char_range Cc0 CLast [chars_bounded2 Cc0]).

