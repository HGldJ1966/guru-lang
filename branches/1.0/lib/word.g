Include "minus.g".
Include "bv.g".
Include "owned.g".

Define wordlen := (mult2 (mult2 (S (S (S (S (S (S (S (S Z)))))))))).

Define primitive word := <bv wordlen> <<END
#define gdelete_word(x)
END.

Untracked word.

Define primitive mkword : Fun(#untracked b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0:bool).#untracked word := 
fun (b31 b30 b29 b28 b27 b26 b25 b24 b23 b22 b21 b20 b19 b18 b17 b16 b15 b14 b13 b12 b11 b10 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 :bool).
cast
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))) b0
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))) b1
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))) b2
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))) b3
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))) b4
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))) b5
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))) b6
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))) b7
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))) b8
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))) b9
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))) b10
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))) b11
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))) b12
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))) b13
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))) b14
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))) b15
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))) b16
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))) b17
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))) b18
  (bvc (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))) b19
  (bvc (S (S (S (S (S (S (S (S (S (S (S Z))))))))))) b20
  (bvc (S (S (S (S (S (S (S (S (S (S Z)))))))))) b21
  (bvc (S (S (S (S (S (S (S (S (S Z))))))))) b22
  (bvc (S (S (S (S (S (S (S (S Z)))))))) b23
  (bvc (S (S (S (S (S (S (S Z))))))) b24
  (bvc (S (S (S (S (S (S Z)))))) b25
  (bvc (S (S (S (S (S Z))))) b26
  (bvc (S (S (S (S Z)))) b27
  (bvc (S (S (S Z))) b28
  (bvc (S (S Z)) b29
  (bvc (S Z) b30
  (bvc Z b31 bvn))))))))))))))))))))))))))))))))
by cong <bv *> join
  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))) wordlen
<<END
inline int gmkword(int b31, int b30, int b29, int b28, int b27, int b26, int b25, int b24, int b23, int b22, int b21, int b20, int b19, int b18, int b17, int b16, int b15, int b14, int b13, int b12, int b11, int b10, int b9, int b8, int b7, int b6, int b5, int b4, int b3, int b2, int b1, int b0) {
  return (b31 << 31) | (b30  << 30) | (b29  << 29) | (b28  << 28) | (b27  << 27) | (b26  << 26) | (b25  << 25) | (b24  << 24) | (b23  << 23) | (b22  << 22) | (b21  << 21) | (b20  << 20) | (b19  << 19) | (b18  << 18) | (b17  << 17) | (b16  << 16) | (b15  << 15) | (b14  << 14) | (b13  << 13) | (b12  << 12) | (b11  << 11) | (b10  << 10) | (b9 << 9) | (b8 << 8) | (b7 << 7) | (b6 << 6) | (b5 << 5) | (b4 << 4) | (b3 << 3) | (b2 << 2) | (b1 << 1) | (b0 << 0);
}
END.


%=============================================================================
% word constants
%=============================================================================

Define primitive word0 : word := (mkvec bool ff wordlen) <<END
#define gword0 0
END.

Define word_max := 0xffffffff.

% DEPRECATED
Define word1 := 0x1.
Define word2 := 0x2.
Define word3 := 0x3.
Define word4 := 0x4.
Define word5 := 0x5.
Define word6 := 0x6.
Define word7 := 0x7.
Define word8 := 0x8.
Define word9 := 0x9.
Define word0x1f := 0x1f.
Define word0x20 := 0x20.


%=============================================================================
% word and nat
%=============================================================================

Define spec word_to_nat := (to_nat wordlen).
Define word_to_nat_tot := [to_nat_tot wordlen].
Total word_to_nat word_to_nat_tot.

Define word_neq_to_nat_neq :
  Forall(w w':word)(u:{ w != w' }).
    { (to_nat w) != (to_nat w') }
  := foralli(w w':word)(u:{ w != w' }).
       diseqi foralli(v: { (to_nat w) = (to_nat w') }).
                contra
                  trans [to_nat_inj wordlen w w' v]
                        symm u
                False.

%-
 to_bv_trimmed : a different version of to_bv
          converts a nat ``n'' to a bv with a specific length ``l''
          (dropping the most significant bits)
-%
Define to_bv_trimmed : Fun(l n:nat).<bv l> := 
  fun to_bv_trimmed(l n:nat):<bv l>.
    match l with
      Z => cast bvn by cong <bv *> symm l_eq
    | S l' => cast (bvc l' (mod2 n) (to_bv_trimmed l' (div2 n))) by
                cong <bv *> symm l_eq
    end.

Define to_bv_trimmed_total : Forall(l n:nat).Exists(r:<bv l>).
                       { (to_bv_trimmed l n) = r } :=
  foralli(l:nat).
  case l with
    Z =>
      foralli(n:nat).
        abbrev r = cast bvn by cong <bv *> symm l_eq in
        existsi r { (to_bv_trimmed l n) = * }
                hypjoin (to_bv_trimmed l n) r by l_eq end
  | S l' =>
      foralli(n:nat).
        abbrev r = cast (bvc l' (mod2 n) (to_bv_trimmed l' (div2 n))) by
                     cong <bv *> symm l_eq
        in
        existsi r { (to_bv_trimmed l n) = * }
                hypjoin (to_bv_trimmed l n) r by l_eq end
  end.

Total to_bv_trimmed to_bv_trimmed_total.

Define spec nat_to_word : Fun(n:nat).word :=
  fun(n:nat).
    (to_bv_trimmed wordlen n).
    
Define nat_to_word_total :=
  foralli(n:nat).
  existsi (to_bv_trimmed wordlen n) { (nat_to_word n) = * }
    join (nat_to_word n) (to_bv_trimmed wordlen n)
  .

Total nat_to_word nat_to_word_total.

Define trusted word_to_nat_to_word :
  Forall(b:word).
    { (nat_to_word (to_nat b)) = b }
  := truei.

Define trusted nat_to_word_to_nat :
  Forall(n:nat)
        (u:{ (le n (to_nat word_max)) = tt }).
    { (to_nat (nat_to_word n)) = n }
  := truei.


%=============================================================================
% word equality
%=============================================================================

Define primitive eqword : Fun(w1 w2:word).bool := (eqbv wordlen) <<END
inline int geqword(int w1,int w2) {
  return (w1 == w2);
}
END.

Define eqword_eq := [eqbv_eq wordlen].
Define eqword_tot := [eqbv_tot wordlen].
Total eqword eqword_tot.
Define eqword_refl := [eqbv_refl wordlen].
Define eqword_symm := [eqbv_symm wordlen].
Define eqword_trans := [eqbv_trans wordlen].
Define eqword_neq := [eqbv_neq wordlen].
Define neq_wordneq := [neq_bvneq wordlen].

Define eqword_ff_neq :
  Forall(w w':word)(u:{ (eqword w w') = ff }).
    { w != w' }
  := foralli(w w':word)(u:{ (eqword w w') = ff }).
       [eqword_neq w w' u].


%=============================================================================
% word comparison
%=============================================================================

Define primitive ltword : Fun(#untracked w1 w2:word).bool :=
  fun(w1 w2:word).
  (lt (word_to_nat w1) (word_to_nat w2))<<END
  int gltword(unsigned int w1, unsigned int w2) { return (w1 < w2); }
END.

Define primitive leword : Fun(#untracked w1 w2:word).bool :=
  fun(w1 w2:word).
  (le (word_to_nat w1) (word_to_nat w2)) <<END
  int gleword(unsigned int w1, unsigned int w2) { return (w1 <= w2); }
END.

Define ltword_total :
  Forall(w1 w2:word).Exists(b:bool).
    { (ltword w1 w2) = b }
  := foralli(w1 w2:word).
       existsi (lt (word_to_nat w1) (word_to_nat w2))
         { (ltword w1 w2) = *}
         join (ltword w1 w2) (lt (word_to_nat w1) (word_to_nat w2)).

Total ltword ltword_total.

Define leword_total :
  Forall(w1 w2:word).Exists(b:bool).
    { (leword w1 w2) = b }
  := foralli(w1 w2:word).
       existsi (le (word_to_nat w1) (word_to_nat w2))
         { (leword w1 w2) = *}
         join (leword w1 w2) (le (word_to_nat w1) (word_to_nat w2)).

Total leword leword_total.

Define ltword_to_lt :=	% useful to avoid evaluating subterms
  foralli(w1 w2:word).
  join (ltword w1 w2) (lt (to_nat w1) (to_nat w2))
  .

Define leword_to_le :=	% useful to avoid evaluating subterms
  foralli(w1 w2:word).
  join (leword w1 w2) (le (to_nat w1) (to_nat w2))
  .

Define leword_refl :=
  foralli(w:word).
  trans join (leword w w) (le (to_nat w) (to_nat w))
        [le_refl (word_to_nat w)].

Define ltword_implies_leword :
  Forall(a b:word)(u:{ (ltword a b) = tt }).{ (leword a b) = tt }
  :=
  foralli(a b:word)(u:{ (ltword a b) = tt }).
  abbrev u' = hypjoin (lt (to_nat a) (to_nat b)) tt by u end in
  abbrev p1 = [lt_implies_le (word_to_nat a) (word_to_nat b) u'] in
  hypjoin (leword a b) tt by p1 end.

Define ltword_implies_neq : Forall(a b:word)(u:{ (ltword a b) = tt }). { a != b }
	:=
	foralli(a b:word)(u:{ (ltword a b) = tt }).
	case (eqword a b) by q1 _ with
		ff =>
			[eqword_ff_neq a b q1]
	| tt =>
			contra
			abbrev p1 = trans symm [ltword_to_lt a b] u in
			abbrev p2 = [lt_implies_neq (word_to_nat a) (word_to_nat b) p1] in
			abbrev p3 = [eqword_eq a b q1] in
			trans cong (to_nat *) p3
						symm p2
			{ a != b }
	end.
				
Define leword_word0 : Forall(w:word).{ (leword word0 w) = tt }
	:=
	foralli(w:word).
	trans join (leword word0 w) (le Z (to_nat w))
				[leZ (word_to_nat w)]
	.

Define trusted leword_word_max : Forall(w:word).{ (leword w word_max) = tt } := truei.

Define ltword_trans :
  Forall(a b c:word)
        (u1: { (ltword a b) = tt })
        (u2: { (ltword b c) = tt }).
    { (ltword a c) = tt }
  := 
  foralli(a b c:word)
         (u1: { (ltword a b) = tt })
         (u2: { (ltword b c) = tt }).
   hypjoin (ltword a c) tt
   by
     [lt_trans (word_to_nat a) (word_to_nat b) (word_to_nat c)
       hypjoin (lt (word_to_nat a) (word_to_nat b)) tt by u1 end
       hypjoin (lt (word_to_nat b) (word_to_nat c)) tt by u2 end]
   end.

Define leltword_trans :
  Forall(a b c:word)
        (u1: { (leword a b) = tt })
        (u2: { (ltword b c) = tt }).
    { (ltword a c) = tt }
  := 
  foralli(a b c:word)
         (u1: { (leword a b) = tt })
         (u2: { (ltword b c) = tt }).
   hypjoin (ltword a c) tt
   by
     [lelt_trans (word_to_nat a) (word_to_nat b) (word_to_nat c)
       hypjoin (le (word_to_nat a) (word_to_nat b)) tt by u1 end
       hypjoin (lt (word_to_nat b) (word_to_nat c)) tt by u2 end]
   end.

Define ltleword_trans :
  Forall(a b c:word)
        (u1: { (ltword a b) = tt })
        (u2: { (leword b c) = tt }).
    { (ltword a c) = tt }
  := 
  foralli(a b c:word)
         (u1: { (ltword a b) = tt })
         (u2: { (leword b c) = tt }).
   hypjoin (ltword a c) tt
   by
     [ltle_trans (word_to_nat a) (word_to_nat b) (word_to_nat c)
       hypjoin (lt (word_to_nat a) (word_to_nat b)) tt by u1 end
       hypjoin (le (word_to_nat b) (word_to_nat c)) tt by u2 end]
   end.

Define word_comp := (ucomparator word ltword leword).

Define trusted ltword_implies_ltword_word_max :
  Forall(a b:word)(u:{ (ltword a b) = tt }).
    { (ltword a word_max) = tt }
  := truei.

Define trusted ltword_implies_lt_word_max :
  Forall(a b:word)(u:{ (ltword a b) = tt }).
    { (lt (to_nat a) (to_nat word_max)) = tt }
  := truei.

Define le_word_implies_le_word_max :
  Forall(n:nat)(w:word)(u:{ (le n (to_nat w)) = tt }).
    { (le n (to_nat word_max)) = tt }
  :=
  foralli(n:nat)(w:word)(u:{ (le n (to_nat w)) = tt }).
  abbrev p1 =
		trans symm [leword_to_le w word_max]
					[leword_word_max w]
		in
	[le_trans n (word_to_nat w) (word_to_nat word_max) u p1]
	.

Define lt_word_implies_le_word_max :
  Forall(n:nat)(w:word)(u:{ (lt n (to_nat w)) = tt }).
    { (le n (to_nat word_max)) = tt }
  :=
  foralli(n:nat)(w:word)(u:{ (lt n (to_nat w)) = tt }).
  abbrev p1 = [lt_implies_le n (word_to_nat w) u] in
  [le_word_implies_le_word_max n w p1].

Define lt_to_nat_ltword :
  Forall(n:nat)(w:word)(u:{ (lt n (to_nat w)) = tt }).
    { (ltword (nat_to_word n) w) = tt }
  :=
  foralli(n:nat)(w:word)(u:{ (lt n (to_nat w)) = tt }).
  abbrev p1 = [lt_word_implies_le_word_max n w u] in
  trans [ltword_to_lt (nat_to_word n) w]
  trans cong (lt * (to_nat w)) [nat_to_word_to_nat n p1]
  			u
  .

Define trusted le_to_nat_leword :
  Forall(n:nat)(w:word)(u:{ (le n (to_nat w)) = tt }).
    { (leword (nat_to_word n) w) = tt }
  := truei.

%=============================================================================
% word incrementing
%=============================================================================

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
void *gword_inc(unsigned int c) {
  return gmk_word_inc_t(c+1, (c == UINT_MAX));
}
END.

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

Total word_inc word_inc_tot.

Define trusted word_inc_implies_ltword :
  Forall(w w':word)(u:{ (word_inc w) = (mk_word_inc_t w' ff) }).
    { (ltword w w') = tt }
  := truei.


Define word_inc2 :=
  fun(b:word).
    match (word_inc b) with
      mk_word_inc_t b' carry => 
        match carry with
          ff => b'
        | tt => abort word
        end
    end.

Define word_inc2_word_inc
  : Forall(w w':word)(u:{ w' = (word_inc2 w) }).
          { (word_inc w) = (mk_word_inc_t w' ff) }
	:=
	foralli(w w':word)(u:{ w' = (word_inc2 w) }).
	existse [word_inc_tot w]
	foralli(r:word_inc_t)(r_pf:{ (word_inc w) = r }).
	case r with mk_word_inc_t x b =>
	case b with
		ff =>
			hypjoin (word_inc w) (mk_word_inc_t w' ff) by u b_eq r_pf r_eq end
	| tt =>
			contra
				trans hypjoin w' abort ! by r_pf r_eq b_eq u end
							aclash w'
				{ (word_inc w) = (mk_word_inc_t w' ff) }
	end end.

Define word_inc2_implies_ltword :
  Forall(w w':word)(u:{ w' = (word_inc2 w) }).{ (ltword w w') = tt }
  :=
  foralli(w w':word)(u:{ w' = (word_inc2 w) }).
	abbrev p1 = [word_inc2_word_inc w w' u] in
	[word_inc_implies_ltword w w' p1].


Define primitive word_inc_safe :=
  fun(b:word)(u:{ (ltword b word_max) = tt }).
  (word_inc2 b) <<END
  #define gword_inc_safe(b) (b+1)
END.

Define trusted word_inc_safe_total :
  Forall(b:word)(u:{ (ltword b word_max) = tt }).
  Exists(b':word).
    { (word_inc_safe b) = b' }
  := truei.

Total word_inc_safe word_inc_safe_total.

Define word_inc_safe_implies_ltword :
  Forall(w w':word)(u:{ w' = (word_inc_safe w) }).
    { (ltword w w') = tt }
  :=
  foralli(w w':word)(u:{ w' = (word_inc_safe w) }).
  abbrev u' = hypjoin w' (word_inc2 w) by u end in
  [word_inc2_implies_ltword w w' u'].


Define word_to_nat_inc
   : Forall(w w2:word)(carry:bool)
           (u : { (word_inc w) = (mk_word_inc_t w2 carry)}).
      { (S (to_nat w)) = (condplus carry (pow2 wordlen)
                                 (to_nat w2)) } :=
  foralli(w w2:word)(carry:bool)
         (u : { (word_inc w) = (mk_word_inc_t w2 carry)}).
    existse cinv (bv_inc wordlen w)
              trans symm eval (word_inc w) u
    induction(r:<bv_inc_t wordlen>) return
      Forall(u2:{(bv_inc w) = r}).
        { (S (to_nat w)) = (condplus carry (pow2 wordlen)
                                  (to_nat w2)) } with
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
      { (S (to_nat w)) = (to_nat w2) } :=
   foralli(w w2:word)
           (u : { (word_inc w) = (mk_word_inc_t w2 ff)}).
     trans [word_to_nat_inc w w2 ff u]
           [condplusff terminates (pow2 wordlen) by pow_total
              terminates (word_to_nat w2) by word_to_nat_tot].

Define word_inc2_word_to_nat
  : Forall(w w2:word)
          (u:{ w2 = (word_inc2 w) }).
      { (S (to_nat w)) = (to_nat w2) }
  :=
  foralli(w w2:word)
         (u:{ w2 = (word_inc2 w) }).
  abbrev p = [word_inc2_word_inc w w2 u] in
  [word_to_nat_inc2 w w2 p]
  .

Define trusted word_inc_safe_word_to_nat
  : Forall(w:word)
          (u:{ (ltword w word_max) = tt}).
      { (to_nat (word_inc_safe w)) = (S (to_nat w)) }
  := truei.


%=============================================================================
% word decrementing
%=============================================================================

Define primitive word_dec_safe :=
  fun(b:word)
     (u:{ (ltword word0 b) = tt }).
  (nat_to_word (minus (word_to_nat b) (S Z))) <<END
  inline unsigned int gword_dec_safe( unsigned int b) { return b-1; }
END.

Define trusted ltword_implies_ltword_word0 :
  Forall(w w':word)(u:{ (ltword w' w) = tt }).
    { (ltword word0 w) = tt }
  := truei.


%=============================================================================
% word individual bit operations
%=============================================================================

Define primitive word_read_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). bool :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_get bool wordlen w (to_nat wordlen i) u) <<END
inline unsigned int gword_read_bit(unsigned int i, unsigned int w) {
    return  (w >> i) & 1;
}
END.

Define primitive word_set_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) tt u) <<END
inline unsigned int gword_set_bit(unsigned int i, unsigned int w) {
    return  ((1 << i) | w);
}
END.

Define primitive word_clear_bit
 : Fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word). word :=
   fun(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    (vec_update bool wordlen w (to_nat wordlen i) ff u) <<END
inline unsigned int gword_clear_bit(unsigned int i, unsigned int w) {
    return (~(1 << i) & w);
}
END.

Define word_set_read :
  Forall(w:word)
        (i:word)
        (u:{ (lt (to_nat i) wordlen) = tt }).
    { (word_read_bit i (word_set_bit i w)) = tt }
  :=
  foralli(w:word)(i:word)
         (u:{ (lt (to_nat i) wordlen) = tt }).
  hypjoin (word_read_bit i (word_set_bit i w))
          tt
          by [vec_update_get bool wordlen w (to_nat wordlen i) tt u] end
  .

Define word_clear_read :
  Forall(w:word)
        (i:word)
        (u:{ (lt (to_nat i) wordlen) = tt }).
    { (word_read_bit i (word_clear_bit i w)) = ff }
  :=
  foralli(w:word)(i:word)
         (u:{ (lt (to_nat i) wordlen) = tt }).
  hypjoin (word_read_bit i (word_clear_bit i w))
          ff
          by [vec_update_get bool wordlen w (to_nat wordlen i) ff u] end
  .

Define word_read_msb :=
  fun(w:word).
    abbrev p = join (lt (to_nat word0x1f) wordlen) tt in
    (word_read_bit word0x1f p w).

Define word_set_msb :=
  fun(w:word).
    abbrev p = join (lt (to_nat word0x1f) wordlen) tt in
    (word_set_bit word0x1f p w).

Define word_clear_msb :=
  fun(w:word).
    abbrev p = join (lt (to_nat word0x1f) wordlen) tt in
    (word_clear_bit word0x1f p w).

Define word_msb := word_read_msb.

Define word_read_bit_total :
  Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
  Exists(b:bool).
    { (word_read_bit i w) = b }
  := 
  foralli(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    existse [vec_get_tot bool wordlen w (to_nat wordlen i) u]
    foralli (b:bool)(b_eq: { (vec_get w (to_nat i)) = b }).
      existsi b
        { (word_read_bit i w) = * }
        trans join (word_read_bit i w) (vec_get w (to_nat i))
              b_eq.        

Total word_read_bit word_read_bit_total.

Define word_set_bit_total :
  Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
  Exists(w':word).
    { (word_set_bit i w) = w' }
  := 
  foralli(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    existse [vec_update_tot bool wordlen w (to_nat wordlen i) tt u]
    foralli (l:<vec bool wordlen>)(l_eq: { (vec_update w (to_nat i) tt) = l }).
      existsi l
        { (word_set_bit i w) = * }
        trans join (word_set_bit i w) (vec_update w (to_nat i) tt)
              l_eq.        

Total word_set_bit word_set_bit_total.

Define word_clear_bit_total :
  Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
  Exists(w':word).
    { (word_clear_bit i w) = w' }
  := 
  foralli(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
    existse [vec_update_tot bool wordlen w (to_nat wordlen i) ff u]
    foralli (l:<vec bool wordlen>)(l_eq: { (vec_update w (to_nat i) ff) = l }).
      existsi l
        { (word_clear_bit i w) = * }
        trans join (word_clear_bit i w) (vec_update w (to_nat i) ff)
              l_eq.        

Total word_clear_bit word_clear_bit_total.

Define word_read_msb_total :
  Forall(w:word).Exists(b:bool).{ (word_read_msb w) = b }
  := 
  foralli(w:word).
  existse [word_read_bit_total word0x1f join (lt (to_nat word0x1f) wordlen) tt w]
  foralli(b:bool)(b_eq:{ (word_read_bit word0x1f w) = b }).
    existsi b
    { (word_read_msb w) = * }
    trans join (word_read_msb w) (word_read_bit word0x1f w)
          b_eq.
Total word_read_msb word_read_msb_total.

Define word_set_msb_total :
  Forall(w:word).Exists(w':word).{ (word_set_msb w) = w' }
  := 
  foralli(w:word).
  existse [word_set_bit_total word0x1f join (lt (to_nat word0x1f) wordlen) tt w]
  foralli(w':word)(w'_eq:{ (word_set_bit word0x1f w) = w' }).
    existsi w'
    { (word_set_msb w) = * }
    trans join (word_set_msb w) (word_set_bit word0x1f w)
          w'_eq.
Total word_set_msb word_set_msb_total.

Define word_clear_msb_total :
  Forall(w:word).Exists(w':word).{ (word_clear_msb w) = w' }
  := 
  foralli(w:word).
  existse [word_clear_bit_total word0x1f join (lt (to_nat word0x1f) wordlen) tt w]
  foralli(w':word)(w'_eq:{ (word_clear_bit word0x1f w) = w' }).
    existsi w'
    { (word_clear_msb w) = * }
    trans join (word_clear_msb w) (word_clear_bit word0x1f w)
          w'_eq.
Total word_clear_msb word_clear_msb_total.


Define word_set_clear :
  Forall(w:word)
        (i:word)
        (u:{ (lt (to_nat i) wordlen) = tt }).
    { (word_clear_bit i (word_set_bit i w)) = (word_clear_bit i w) }
  :=
  foralli(w:word)(i:word)
         (u:{ (lt (to_nat i) wordlen) = tt }).
  abbrev p1 = [vec_update_twice bool wordlen w (word_to_nat i) tt ff u] in
  hypjoin (word_clear_bit i (word_set_bit i w))
          (word_clear_bit i w)
    by p1 end
  .

Define word_clear_set :
  Forall(w:word)
        (i:word)
        (u:{ (lt (to_nat i) wordlen) = tt }).
    { (word_set_bit i (word_clear_bit i w)) = (word_set_bit i w) }
  :=
  foralli(w:word)(i:word)
         (u:{ (lt (to_nat i) wordlen) = tt }).
  abbrev p1 = [vec_update_twice bool wordlen w (word_to_nat i) ff tt u] in
  hypjoin (word_set_bit i (word_clear_bit i w))
          (word_set_bit i w)
    by p1 end
  .

Define trusted word_msb_tt_set_msb :
  Forall(w:word)(u:{ (word_msb w) = tt }).
  	{ (word_set_msb w) = w }
	:= truei.

Define trusted word_msb_ff_clear_msb :
  Forall(w:word)(u:{ (word_msb w) = ff }).
  	{ (word_clear_msb w) = w }
	:= truei.
  
  
Define trusted word0_set_bit_pow2
  : Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt}).
      { (to_nat (word_set_bit i word0)) = (pow2 (to_nat i)) } :=
  truei.


Define lt_word_set_bit
  : Forall(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
      { (lt Z (to_nat (word_set_bit i w))) = tt } :=
  foralli(i:word)(u:{(lt (to_nat i) wordlen) = tt})(w:word).
  trans
    cong (lt Z (to_nat *)) 
      join (word_set_bit i w) (vec_update w (to_nat i) tt)
    [induction(l:nat)(v:<vec bool l>) 
     return Forall(n:nat)(u:{(lt n l) = tt}).
             {(lt Z (to_nat (vec_update v n tt))) = tt }
     with
       vecn _ => foralli(n:nat)(u:{(lt n l) = tt}).
                 contra
                   transs symm u
                          cong (lt n *) inj <vec ** *> v_Eq
                          [lt_Z n]
                          clash ff tt
                   end
                   {(lt Z (to_nat (vec_update v n tt))) = tt }                                         
     | vecc _ l' b v' => 
         foralli(n:nat)(u:{(lt n l) = tt}).
           case n with
             Z => hypjoin (lt Z (to_nat (vec_update v n tt))) tt
                  by n_eq v_eq end
           | S n' => 
             abbrev P = symm
                        transs symm u
                               cong (lt * l) n_eq
                               cong (lt (S n') *) inj <vec ** *> v_Eq
                               [S_lt_S n' l']
                        end in
             abbrev IH = [v_IH l' v' n' P] in
             case b with
               ff => transs cong (lt Z *) 
                              hypjoin (to_nat (vec_update v n tt))  
                                      (mult two (to_nat (vec_update v' n' tt)))
                              by b_eq v_eq n_eq end
                            cong (lt * (mult two (to_nat (vec_update v' n' tt))))
                              join Z (mult two Z) 
                            [mult_lt one Z (to_nat l' (vec_update bool l' v' n' tt P)) IH]
                     end
             | tt => hypjoin (lt Z (to_nat (vec_update v n tt))) tt
                     by b_eq n_eq v_eq end
             end
           end
     end
   wordlen
   w 
   (to_nat wordlen i) 
   u].

Define trusted word_msb_ff_implies_ltword_word_max :
  Forall(w:word)(u:{ (word_msb w) = ff }).
    { (ltword w word_max) = tt }
  := truei.

Define trusted leword_msb_ff_implies_msb_ff :
  Forall(w w':word)
  			(u1:{ (leword w w') = tt })
  			(u2:{ (word_msb w') = ff }).
    { (word_msb w) = ff }
  := truei.


%=============================================================================
% word bit operations
%=============================================================================

Define primitive word_shift: Fun(x:word)(w:word). word := 
  fun(x:word)(w:word). 
   abbrev P = cong <bv *> join wordlen (S (minus wordlen (S Z))) in
     cast (bv_shift (to_nat wordlen x)
            (minus wordlen (S Z)) cast w by P) by symm P <<END
  inline unsigned int gword_shift(unsigned int x, unsigned int w) {
    return w >> x; }
END.

Define primitive word_or: Fun(x y:word). word :=
  fun(x y:word) . (bv_or wordlen x y) <<END
  inline unsigned int gword_or(unsigned int x, unsigned int y) { return x | y; }
END.


%=============================================================================
% word arithmetic
%=============================================================================

Define primitive word_minus: Fun(x y:word). word :=
  fun(x y:word).
  match (ltword x y) with
    ff =>  % x >= y : no overflow
      (nat_to_word (minus (word_to_nat x) (word_to_nat y)))
  | tt =>  % x < y : x + word_max + 1 - y
      (nat_to_word (minus (plus (word_to_nat x) (S (word_to_nat word_max))) (word_to_nat y)))
  end <<END  
  inline unsigned int gword_minus(unsigned int x, unsigned int y) { return x-y; }
END.

Define trusted word_minus_tot :
  Forall(x y:word).Exists(z:word).{(word_minus x y) = z} := truei.

Total word_minus word_minus_tot.

Define primitive word_plus: Fun(x y:word). word :=
  fun(x y:word). (nat_to_word (plus (word_to_nat x) (word_to_nat y)))
  <<END
  inline unsigned int gword_plus(unsigned int x, unsigned int y) { return x+y; }
END.

Define trusted word_plus_tot :
  Forall(x y:word).Exists(z:word).{(word_plus x y) = z} := truei.

Total word_plus word_plus_tot.

Define primitive word_mult: Fun(x y:word). word :=
  fun(x y:word). (nat_to_word (mult (word_to_nat x) (word_to_nat y))) <<END
  inline unsigned int gword_mult(unsigned int x, unsigned int y) { return x * y; }
END.

Define trusted word_mult_total :
  Forall(x y:word). Exists(z:word). { (word_mult x y) = z } := truei.

Total word_mult word_mult_total.

Define primitive word_div: Fun(x y:word)(u:{ y != word0 }). word :=
  fun(x y:word)(u:{ y != word0 }). word0  %% TODO: complete the model
<<END
  inline unsigned int gword_div(unsigned int x, unsigned int y) { return x / y; }
END.

Define trusted word_div_tot : 
  Forall(x y:word)(u:{ y != word0 }).Exists(z:word).{(word_div x y) = z}
  := truei.

Total word_div word_div_tot.

% this is pretty terrible, but Guru does not have great support fo
% disequality reasoning.
Define word10_neq_word0 : { 0xa != 0x0 } :=
symm
trans join 0x0 (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff vecn))))))))))))))))))))))))))))))))
symm
trans join 0xa  (vecc ff (vecc tt (vecc ff (vecc tt (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff vecn))))))))))))))))))))))))))))))))
ncong
  (vecc ff (vecc * (vecc ff (vecc ** (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff vecn))))))))))))))))))))))))))))))))
  (vecc ff (vecc tt (vecc ff (vecc tt (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff vecn))))))))))))))))))))))))))))))))
  (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff (vecc ff vecn))))))))))))))))))))))))))))))))
 clash tt ff. 

Define primitive word_div10: Fun(x : word). word :=
  fun(x : word). word0  %% TODO: complete the model
<<END
  inline unsigned int gword_div10(unsigned int x) { return x / 10; }
END.

Define trusted word_div10_tot : 
  Forall(x : word).Exists(z : word).{(word_div10 x) = z}
  := truei.

Total word_div10 word_div10_tot.

Define word_div2 := (word_shift word1).

Define trusted word_div2_tot : 
  Forall(x:word).Exists(y:word).{(word_div2 x) = y} := truei.

Total word_div2 word_div2_tot.

Define primitive word_mod10: Fun(x : word). word :=
  fun(x : word). word0  %% TODO: complete the model
<<END
  inline unsigned int gword_mod10(unsigned int x) { return x % 10; }
END.

Define trusted word_mod10_tot : 
  Forall(x : word).Exists(z : word).{(word_mod10 x) = z}
  := truei.

Total word_mod10 word_mod10_tot.


