Include "../guru-lang/lib/mult.g".
Include "../guru-lang/lib/pow.g".

Define multZ' : Forall(n:nat).{ (mult n Z) = Z } :=
 induction(n:nat) return { (mult n Z) = Z } with
   Z => trans cong (mult * Z) n_eq
              join (mult Z Z) Z
 | S n' => trans cong (mult * Z) n_eq
           trans join (mult (S n') Z) (mult n' Z)
                 [n_IH n']
 end.

Define prob2 : Forall(x y z:nat). { (plus (plus y x) z) = (plus x (plus y z)) } :=
  foralli(x y z:nat).
    trans cong (plus * z) [plus_comm y x]
          [plus_assoc x y z].

Define mult_plus' : Forall(x y z :nat).{(mult (plus x y) z) = (plus (mult x z) (mult y z))} :=
  induction(x:nat) return Forall(y z :nat).{(mult (plus x y) z) = (plus (mult x z) (mult y z))}
  with
    Z => 
    foralli(y z :nat).
    trans cong (mult (plus * y) z) x_eq
    trans join (mult (plus Z y) z) (plus (mult Z z) (mult y z))
          symm cong (plus (mult * z) (mult y z)) x_eq
  | S x' =>

    foralli(y z :nat).
    trans cong (mult (plus * y) z) x_eq
    trans join (mult (plus (S x') y) z) (plus z (mult (plus x' y) z))
    trans cong (plus z *) [x_IH x' y z]
    trans symm [plus_assoc z (mult x' z) (mult y z)]
          cong (plus * (mult y z)) 
            trans join (plus z (mult x' z)) (mult (S x') z)  
                  symm cong (mult * z) x_eq

  end.    
            
Define xor_not : Forall(x y : bool). { (xor (not x) y) = (not (xor x y)) } :=
  foralli(x y : bool).
  case x with
    ff => trans cong (xor (not *) y) x_eq
          trans join (xor (not ff) y) (not (xor ff y))
                symm cong (not (xor * y)) x_eq
  | tt => trans cong (xor (not *) y) x_eq
          trans join (xor (not tt) y) y
          trans symm [not_not y]
          trans join (not (not y)) (not (xor tt y))
                symm cong (not (xor * y)) x_eq
  end. 

Define mod2_plus : Forall(n m : nat). { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } :=
  induction(n : nat) return Forall(m:nat). { (mod2 (plus n m)) = (xor (mod2 n) (mod2 m)) } 
  with
    Z => foralli(m:nat).
         trans cong (mod2 (plus * m)) n_eq
         trans join (mod2 (plus Z m)) (xor (mod2 Z) (mod2 m))
               symm cong (xor (mod2 *) (mod2 m)) n_eq
  | S n' => 
    foralli(m:nat).
    trans cong (mod2 (plus * m)) n_eq
    trans join (mod2 (plus (S n') m)) (not (mod2 (plus n' m)))
    trans cong (not *) [n_IH n' m]
    trans symm [xor_not (mod2 n') (mod2 m)]
    trans join (xor (not (mod2 n')) (mod2 m)) (xor (mod2 (S n')) (mod2 m))
          cong (xor (mod2 *) (mod2 m)) symm n_eq
  end.
  