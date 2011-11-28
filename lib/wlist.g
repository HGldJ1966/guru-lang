Include trusted "word.g".
Include "ulist.g".

Define wlist := <ulist word>.
Define wlistn := (unil word).
Define wlistc := (ucons word).
Define wlist_app := fun(^#owned s1:wlist)(s2:wlist). (uappend word s1 s2).
Define wlist_app1 := fun(s1 s2:wlist). let ret = (uappend word (inspect wlist s1) s2) in do (dec wlist s1) ret end.
Define wlisteq := (equlist word eqword).
Define wlist_mem := (ulist_mem word eqword).

Define wlisteqEq : Forall(s1 s2:wlist)(u: {(wlisteq s1 s2) = tt}).
                      { s1 = s2 } :=
  foralli(s1 s2:wlist).
    [equlistEq word s1 s2 eqword eqword_tot eqword_eq].

Define wlisteqTot := 
  foralli(s1 s2:wlist).[equlist_total word eqword eqword_tot s1 s2].

%- copied from char.g, needs some work:

Define word_range
 : Fun(c1 c2 : word)(u : { (le (to_nat c1) (to_nat c2)) = tt }). wlist :=
fun word_range(c1 c2 : word)(u : { (le (to_nat c1) (to_nat c2)) = tt }): <ulist word>.
  match (eqword c1 c2) by v ign with
    ff => abbrev c1_lt_c2 = [eqnat_ff_implies_lt (to_nat c1) (to_nat c2) 
                              [to_nat_neq1 wordlen c1 c2 v] u] in
          (wlistc c1 (word_range (word_inc1 c1) c2
                            trans cong (le * (to_nat c2)) [word_inc1_lem c1 c1_lt_CLast]
                                 [lt_S_le (to_nat c1) (to_nat c2) c1_lt_c2]))
  | tt => wlistn
  end.

Define trusted word_range_member
   : Forall (c1 d c2:word)(u:{(le (to_nat c1) (to_nat c2)) = tt})
            (u1 : { (le c1 d) = tt })(u2: {(le d c2) = tt}).
       { (wlist_mem d (word_range c1 c2)) = tt } := truei.

Define all_words := (word_range Cc0 CLast [words_bounded2 Cc0]).

-%
