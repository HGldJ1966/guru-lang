Include trusted "minus.g".
Include trusted "bv.g".
Include "owned.g".

Define wordlen := (mult2 (mult2 (S (S (S (S (S (S (S (S Z)))))))))).

Define primitive word := <bv wordlen> <<END
#define gdelete_word(x)
END.

Untracked word.

Define primitive eqword : Fun(w1 w2:word).bool := (eqbv wordlen) <<END
  #define geqword(w1,w2) (w1 == w2)
END.

Define eqword_eq := [eqbv_eq wordlen].
Define eqword_tot := [eqbv_tot wordlen].
Total eqword eqword_tot.
Define eqword_refl := [eqbv_refl wordlen].

Inductive word_inc_t : type :=
  mk_word_inc_t : Fun(b:word)(carry:bool).word_inc_t.

Define primitive word_inc :=
  fun( b:word).
    let r = (bv_inc wordlen b) in
    match r with
      mk_bv_inc_t l' v' carry => 
        (mk_word_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
           carry)
      end
<<END
#include <limits.h>
void *gword_inc(int c) {
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

Define trusted word_inc2_carry 
  : Forall(w:word)(carry:bool)(u:{ (word_inc2 w) = (mk_word_inc_t w carry) }).
          { carry = ff } := truei.

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

%-
Define trim_to_wordlen : Fun(l:nat)(v':<bv l>).(l':nat)(v':<bv l'>) :=
  fun trim_to_wordlen(l:nat)(v:<bv l>) : (l':nat)(v':<bv l'>).
  match (nat_comp l wordlen) with
    LT => (trim_to_wordlen (plus l one) (bv_append ...
  | EQ => (wordlen, v)
  | GT => (trim_to_wordlen (minus l one) (bv_tail v))
  end.

Define nat_to_word : Fun(x:nat).(c:bool)(w:word) :=
  fun(x:nat).
    match (to_bv x) with
      mk_to_bv_t l v => match (nat_comp l wordlen) with
      		     	  LT => (ff, (trim_to_wordlen v))
			| EQ => (ff, v)
			| GT => (tt, (trim_to_wordlen v))
			end
    end.
-%

Define primitive word_read_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). bool :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_get bool wordlen w (to_nat wordlen i) u) <<END
inline int gword_read_bit(int i, int w) {
    return  ((1 << i) & w);
}
END.

Define primitive word_set_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) tt u) <<END
inline int gword_set_bit(int i, int w) {
    return  ((1 << i) | w);
}
END.

Define primitive word_clear_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) ff u) <<END
inline int gword_clear_bit(int i, int w) {
    return (~(1 << i) & w);
}
END.

Define primitive word0 : word := (mkvec bool ff wordlen) <<END
#define gword0 0
END.

Define word1 := (word_inc2 word0).
Define word2 := (word_inc2 word1).
Define word3 := (word_inc2 word2).
Define word4 := (word_inc2 word3).
Define word5 := (word_inc2 word4).
Define word8 := (word_set_bit word3 join (lt (to_nat word3) wordlen) tt word0).

Define word7 :=
                (word_set_bit word2 join (lt (to_nat word2) wordlen) tt
                (word_set_bit word1 join (lt (to_nat word1) wordlen) tt
                (word_set_bit word0 join (lt (to_nat word0) wordlen) tt word0))).

Define trusted word0_set_bit_pow2
  : Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt}).
      { (to_nat (word_set_bit i word0)) = (pow2 (to_nat i)) } :=
  truei.

Define primitive word_shift: Fun(x:word)(w:word). word := 
  fun(x:word)(w:word). 
   abbrev P = cong <bv *> join wordlen (S (minus wordlen (S Z))) in
     cast (bv_shift (to_nat wordlen x)
            (minus wordlen (S Z)) cast w by P) by symm P <<END
#define gword_shift(x,w) ((w) >> (x))
END.

Define word_div2 := (word_shift word1).

Define trusted word_div2_tot : 
  Forall(x:word).Exists(y:word).{(word_div2 x) = y} := truei.

Total word_div2 word_div2_tot.

Define primitive word_minus: Fun(x y:word). word :=
  fun(x y:word) . x
  <<END  
  inline int gword_minus(int x, int y) { return x-y; }
END.

Define trusted word_minus_tot :
  Forall(x y:word).Exists(z:word).{(word_minus x y) = z} := truei.

Total word_minus word_minus_tot.

Define primitive word_plus: Fun(x y:word). word :=
  fun(x y:word) . x
  <<END
  inline int gword_plus(int x, int y) { return x+y; }
END.

Define trusted word_plus_tot :
  Forall(x y:word).Exists(z:word).{(word_plus x y) = z} := truei.

Total word_plus word_plus_tot.

Define primitive ltword : Fun(#untracked w1 w2:word).bool :=
  fun(w1 w2:word).
  (lt (word_to_nat w1) (word_to_nat w2))<<END
  int gltword(int w1, int w2) { return (w1 < w2); }
END.

Define primitive leword : Fun(#untracked w1 w2:word).bool :=
  fun(w1 w2:word).
  (le (word_to_nat w1) (word_to_nat w2)) <<END
  int gleword(int w1, int w2) { return (w1 <= w2); }
END.

Define word_comp := (ucomparator word ltword leword).

Define trusted word_div2_shrink :
  Forall(x:word).{(lt (to_nat (word_div2 x)) (to_nat x)) = tt} 
  := truei.

Define trusted word_plus_shrink :
  Forall(x y y':word)
        (u:{(lt (to_nat y) (to_nat y')) = tt}).
  {(lt (to_nat (word_plus x y)) (to_nat (word_plus x y'))) = tt}
  := truei.

Define trusted word_plus_minus_shrink :
  Forall(x y:word).
  {(le (to_nat (word_plus x (word_minus y x))) (to_nat y)) = tt} 
  := truei.

Define trusted word_minus_shrink :
  Forall(x:word).
  {(lt (to_nat (word_minus x word1)) (to_nat x)) = tt}
  := truei.


Define word_clear_read :
  Forall(w:word)
        (i:word)
        (u:{ (lt (to_nat i) wordlen) = tt }).
    { (word_read_bit i u (word_clear_bit i u w)) = ff }
  :=
  foralli(w:word)(i:word)
         (u:{ (lt (to_nat i) wordlen) = tt }).
  hypjoin (word_read_bit i u (word_clear_bit i u w))
          ff
          by [vec_update_get bool wordlen w (to_nat wordlen i) ff u] end
  .
