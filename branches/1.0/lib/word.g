Include trusted "bv.g".

Define wordlen := (mult2 (mult2 (S (S (S (S (S (S (S (S Z)))))))))).

Define primitive word := <bv wordlen> <<END
#define gdelete_word(x)
END.

Define primitive eqword : Fun(#untracked w1 w2:word).bool := (eqbv wordlen) <<END
  #define eqword(w1,w2) (w1 == w2)
END.

Define eqword_eq := [eqbv_eq wordlen].
Define eqword_tot := [eqbv_tot wordlen].
Total eqword eqword_tot.
Define eqword_refl := [eqbv_refl wordlen].

Inductive word_inc_t : type :=
  mk_word_inc_t : Fun(b:word)(carry:bool).word_inc_t.

Define primitive word_inc :=
  fun(b:word).
    let r = (bv_inc wordlen b) in
    match r with
      mk_bv_inc_t l' v' carry => 
        (mk_word_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
           carry)
      end
<<END
#include <limits.h>
gword_inc_t gword_inc(gword c) {
  return gmk_word_inc_t(c+1, (c == UINT_MAX));
}
END.

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

Define primitive word_set_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(#untracked w:word).#untracked word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) tt u) <<END
#define gword_set_bit(i, w) ((1 << i) | w);
END.

Define primitive word_clear_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(#untracked w:word).#untracked word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) ff u) <<END
#define gword_clear_bit(i, w) (~(1 << i) & w)
END.

Define primitive word0 : word := (mkvec bool ff wordlen) <<END
#define gword0 0
END.

Define word1 := (word_inc2 word0).
Define word2 := (word_inc2 word1).
Define word3 := (word_inc2 word2).
Define word8 := (word_set_bit word3 join (lt (to_nat word3) wordlen) tt word0).

Define word7 := (word_set_bit word2 join (lt (to_nat word2) wordlen) tt
                (word_set_bit word1 join (lt (to_nat word1) wordlen) tt
                (word_set_bit word0 join (lt (to_nat word0) wordlen) tt word0))).

Define trusted word0_set_bit_pow2
  : Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt}).
      { (to_nat (word_set_bit i word0)) = (pow2 (to_nat i)) } :=
  truei.
