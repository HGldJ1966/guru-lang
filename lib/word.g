Include "string.g".

Define wordlen := (mult2 (mult2 (S (S (S (S (S (S (S (S Z)))))))))).

Define spec word := <bv wordlen>.

Untracked word.

Define spec word0 : word := (mkvec bool ff wordlen).
Define spec eqword : Fun(w1 w2:word).bool := (eqbv wordlen).
Define eqword_eq := [eqbv_eq wordlen].
Define eqword_tot := [eqbv_tot wordlen].
Total eqword eqword_tot.
Define eqword_refl := [eqbv_refl wordlen].

Inductive word_inc_t : type :=
  mk_word_inc_t : Fun(b:word)(carry:bool).word_inc_t.

Define spec word_inc :=
  fun(b:word).
    let r = (bv_inc wordlen b) in
    match r with
      mk_bv_inc_t l' v' carry => 
        (mk_word_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
           carry)
      end.

Define word_inc2 :=
  fun(b:word).
    match (word_inc b) with
      mk_word_inc_t b' carry => 
        match carry with
          ff => b'
        | tt => abort word
        end
    end.

Define word_inc_tot :=
  foralli(b:word).
    abbrev r = terminates (bv_inc spec wordlen b) by bv_inc_tot in
    case r with
      mk_bv_inc_t l' v' carry =>
        existsi (mk_word_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
                  carry)
          { (word_inc b) = * }
          hypjoin (word_inc b) (mk_word_inc_t v' carry)
          by r_eq end
      end.

Define spec word_to_nat := (to_nat wordlen).
Define word_to_nat_tot := [to_nat_tot wordlen].

Define word_to_nat_inc
   : Forall(w w2:word)(carry:bool)
           (u : { (word_inc w) = (mk_word_inc_t w2 carry)}).
      { (S (word_to_nat w)) = (condplus carry (pow2 wordlen)
                                 (word_to_nat w2)) } :=
  foralli(w w2:word)(carry:bool)
         (u : { (word_inc w) = (mk_word_inc_t w2 carry)}).
    existse cinv (bv_inc wordlen w)
              trans symm eval (word_inc w) u
    induction(r:<bv_inc_t wordlen>) return
      Forall(u2:{(bv_inc w) = r}).
        { (S (word_to_nat w)) = (condplus carry (pow2 wordlen)
                                  (word_to_nat w2)) } with
        mk_bv_inc_t l' v' carry' =>
          abbrev cv' = cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq in
          foralli(u2:{(bv_inc w) = r}).
            abbrev P = trans symm u
                         hypjoin (word_inc w) (mk_word_inc_t v' carry')
                         by u2 r_eq end in
            trans [to_nat_bv_inc wordlen w cv' carry' trans u2 r_eq] 
            trans cong (condplus * (pow2 wordlen) (to_nat v'))
                    symm inj (mk_word_inc_t ** *) P
                  cong (condplus carry (pow2 wordlen) (to_nat *))
                    symm inj (mk_word_inc_t * **) P
    end.

Define word_to_nat_inc2
   : Forall(w w2:word)
           (u : { (word_inc w) = (mk_word_inc_t w2 ff)}).
      { (S (word_to_nat w)) = (word_to_nat w2) } :=
   foralli(w w2:word)
           (u : { (word_inc w) = (mk_word_inc_t w2 ff)}).
     trans [word_to_nat_inc w w2 ff u]
           [condplusff terminates (pow2 wordlen) by pow_total
              terminates (word_to_nat w2) by word_to_nat_tot].

Define spec char_to_word : Fun(c:char).word :=
  fun(c:char).
  cast
   (bv_append charlen (minus wordlen charlen) c (mkvec bool ff (minus wordlen charlen)))
  by cong <vec bool *> [plus_minus charlen wordlen join (lt charlen wordlen) tt]. 