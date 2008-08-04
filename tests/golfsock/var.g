Include "../../lib/word.g".

Define var := word.
Define eqvar := eqword.
Define eqvarEq := eqword_eq.
Define eqvarTot := eqword_tot.
Define v2n := word_to_nat.
Define v2n_tot := word_to_nat_tot.
Define spec vlt := fun(n m:var).(lt (v2n n) (v2n m)).
Define spec vle := fun(n m:var).(le (v2n n) (v2n m)).
Define vS := word_inc.
Define vS_tot := word_inc_tot.

Define vlt_total := 
  foralli(a b:var).
   abbrev r = terminates 
                (lt terminates (v2n a) by v2n_tot 
                    terminates (v2n b) by v2n_tot)
              by lt_total in
  existsi r {(vlt a b) = *} join (vlt a b) r.

Define vltle_trans := 
  foralli(a b c:var)
         (u1:{(vlt a b) = tt})
         (u2:{(vle b c) = tt}).
  hypjoin (vlt a c) tt
  by
   [ltle_trans 
      terminates (v2n a) by v2n_tot
      terminates (v2n b) by v2n_tot
      terminates (v2n c) by v2n_tot
      hypjoin (lt (v2n a) (v2n b)) tt
        by u1 end
      hypjoin (le (v2n b) (v2n c)) tt
        by u2 end]
  end.
Define vlelt_trans := 
  foralli(a b c:var)
         (u1:{(vle a b) = tt})
         (u2:{(vlt b c) = tt}).
  hypjoin (vlt a c) tt
  by
   [lelt_trans 
      terminates (v2n a) by v2n_tot
      terminates (v2n b) by v2n_tot
      terminates (v2n c) by v2n_tot
      hypjoin (le (v2n a) (v2n b)) tt
        by u1 end
      hypjoin (lt (v2n b) (v2n c)) tt
        by u2 end]
  end.
Define vlt_trans := 
  foralli(a b c:var)
         (u1:{(vlt a b) = tt})
         (u2:{(vlt b c) = tt}).
  hypjoin (vlt a c) tt
  by
   [lt_trans 
      terminates (v2n a) by v2n_tot
      terminates (v2n b) by v2n_tot
      terminates (v2n c) by v2n_tot
      hypjoin (lt (v2n a) (v2n b)) tt
        by u1 end
      hypjoin (lt (v2n b) (v2n c)) tt
        by u2 end]
  end.
Define vle_trans := 
  foralli(a b c:var)
         (u1:{(vle a b) = tt})
         (u2:{(vle b c) = tt}).
  hypjoin (vle a c) tt
  by
    [le_trans 
      terminates (v2n a) by v2n_tot
      terminates (v2n b) by v2n_tot
      terminates (v2n c) by v2n_tot
      hypjoin (le (v2n a) (v2n b)) tt
        by u1 end
      hypjoin (le (v2n b) (v2n c)) tt
        by u2 end]
  end.

Define vlt_implies_vle :=
  foralli(a b:var)
         (u:{(vlt a b) = tt}).
    hypjoin (vle a b) tt
      by [lt_implies_le 
           terminates (v2n a) by v2n_tot
           terminates (v2n b) by v2n_tot
           hypjoin (lt (v2n a) (v2n b)) tt
            by u end]
      end.

Define x_vle_x :=
  foralli(a:var).
    hypjoin (vle a a) tt
     by [x_le_x terminates (v2n a) by v2n_tot] end.

Define vlt_S :=
  foralli(a:var)(b:var)
         (u:{(vS a) = (mk_word_inc_t b ff)}).
    trans join (vlt a b)
               (lt (v2n a) (v2n b))
    trans cong (lt (v2n a) *) 
           symm [word_to_nat_inc2 a b
                  trans join (word_inc a) (vS a)
                    u]
      [lt_S terminates (v2n a) by v2n_tot].

Define vle_S :=
  foralli(a:var)(b:var)
         (u:{(vS a) = (mk_word_inc_t b ff)}).
    [vlt_implies_vle a b [vlt_S a b u]].

