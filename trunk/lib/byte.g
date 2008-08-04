Include "char.g".

Define bytelen := (S (S (S (S (S (S (S (S Z)))))))).

Define num_bytes := (pow2 (S bytelen)).

Define spec byte := <bv bytelen>.

Untracked byte.

% least significant bit comes first (according to to_nat in bv.g)

Define spec mkbyte : Fun(b7 b6 b5 b4 b3 b2 b1 b0:bool).byte := 
  fun (b7 b6 b5 b4 b3 b2 b1 b0:bool).
    (bvc (S (S (S (S (S (S (S Z))))))) b7
    (bvc (S (S (S (S (S (S Z)))))) b6
    (bvc (S (S (S (S (S Z))))) b5
    (bvc (S (S (S (S Z)))) b4
    (bvc (S (S (S Z))) b3
    (bvc (S (S Z)) b2
    (bvc (S Z) b1
    (bvc Z b0 bvn)))))))).

Define byte0 := (mkbyte ff ff ff ff ff ff ff ff).
Define byte1 := (mkbyte tt ff ff ff ff ff ff ff).

Define spec eqbyte : Fun(c1 c2:byte).bool := (eqvec bool bytelen iff).

Define spec char_to_byte : Fun(c:char).byte := 
  % recall from bv.g that the least significant bit is listed first,
  % so we must slap our leading 0 on the end of the character.
  fun (c:char). 
    cast (bv_append charlen (S Z) c (bvc Z ff bvn)) by
    cong <bv *> join (plus charlen (S Z)) bytelen.

Inductive byte_inc_t : type :=
  mk_byte_inc_t : Fun(b:byte)(carry:bool).byte_inc_t.

Define spec byte_inc :=
  fun(b:byte).
    let r = (bv_inc bytelen b) in
    match r with
      mk_bv_inc_t l' v' carry => 
        (mk_byte_inc_t cast v' by cong <bv *> symm inj <bv_inc_t *> r_Eq 
           carry)
      end.

Define spec which_byte : Fun(c:byte).nat := (to_nat bytelen). 

Define eqbyte_tot : Forall(c1 c2:byte).Exists(b:bool).
                         { (eqbyte c1 c2) = b } := 
  [eqvec_tot bool iff iff_tot bytelen].

Define eqbyte_eq : Forall(c1 c2:byte)(u:{(eqbyte c1 c2) = tt}).
                   { c1 = c2 } := 
  [eqvec_eq bool iff iff_eq bytelen].

Define bytes_bounded
 : Forall(c:byte). { (lt (which_byte c) num_bytes) = tt } :=
   foralli(c:byte). [lt_to_nat bytelen c].  

