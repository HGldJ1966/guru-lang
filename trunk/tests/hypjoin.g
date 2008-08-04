Set "print_parsed".

Inductive nat : type :=
  Z : nat
| S : Fun(x:nat).nat.

Define plus : Fun(n m : nat). nat :=
  fun plus(n m : nat):nat. 
    match n by x y return nat with
      Z => m
    | S n' => (S (plus n' m))
    end.

Define plusZ : Forall(n:nat). { (plus n Z) = n } :=
  induction(n:nat) by x1 x2 IH return { (plus n Z) = n } with
    Z => hypjoin (plus n Z) n by x1 end
  | S n' => hypjoin (plus n Z) n by x1 [IH n'] end
  end.
  
Define plus_assoc : Forall(x y z:nat). 
                    { (plus (plus x y) z) = (plus x (plus y z)) } :=
  induction(x:nat) by x1 x2 IH return 
                   Forall(y z : nat). 
                     { (plus (plus x y) z) = (plus x (plus y z)) }
  with
    Z => foralli(y z : nat). 
         hypjoin (plus (plus x y) z) (plus x (plus y z)) by x1 end
  | S x' => foralli(y z : nat). 
  			hypjoin (plus (plus x y) z) (plus x (plus y z)) by x1 [IH x' y z] end
 
end.

Inductive bool : type :=
  T : bool
| F : bool.

Define ge :=
  fun ge(n m:nat) : bool.
    match m by m1 m2 return bool with
      Z => T
   | S m' => match n by n1 n2 return bool with
       Z => F
     | S n' => (ge n' m')
     end
   end. 

Define geRefl : Forall(n:nat). { (ge n n) = T } :=
	induction(n:nat) by x1 x2 IH return { (ge n n) = T} with
		Z => hypjoin (ge n n) T by x1 end
	| S n' => hypjoin (ge n n) T by x1 [IH n'] end
              
	end.
	
Define sGE : Forall(n: nat). { (ge (S n) n) = T } :=
  induction(n:nat) by x1 x2 IH return { (ge (S n) n) = T} with
    Z => hypjoin (ge (S n) n) T by x1 end
	| S n' => hypjoin (ge (S n) n) T by x1 [IH n'] end
	end.
  

Define geZ : Forall(n : nat)(a1 : {(ge Z n) = T}). {n = Z} :=
  induction(n:nat) by x1 x2 IH return Forall(a1:{(ge Z n) = T}). {n = Z} with
    Z => foralli(a1 : {(ge Z n) = T}).x1
  | S n' => foralli(a1 : {(ge Z n) = T}).
              contra
                trans hypjoin T F by symm a1 x1 end
                  clash F T
                {n = Z}
  end.
  
Define geTrans : Forall(a b c : nat)(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}). {(ge a c) = T} :=
  induction(a:nat) by x1 x2 IH return Forall(b c : nat)(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}). {(ge a c) = T}  with
    Z => foralli(b c : nat)(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}). 
    	hypjoin (ge a c) T by 
    	[geZ c trans symm cong (ge * c)
    	[geZ b trans symm cong (ge * b) x1 a1]
    	a2]
    	end
  | S a' => induction(b:nat) by ix1 ix2 IIH return Forall(c : nat)(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}). {(ge a c) = T}  with
      Z => foralli(c : nat)(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}).
            hypjoin (ge a c) T by
              [geZ c symm trans symm a2 cong (ge * c) ix1]
              end
    | S b' => induction(c:nat) by iix1 iix2 IIIH return Forall(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}). {(ge a c) = T}  with
          Z => foralli(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}).
            hypjoin (ge a c) T by iix1 end
        | S c' => foralli(a1 : { (ge a b) = T})(a2 : { (ge b c) = T}).
        	  hypjoin (ge a c) T by x1 iix1
              [IH a' b' c'
              trans hypjoin (ge a' b') (ge a b) by x1 ix1 end a1
              trans hypjoin (ge b' c') (ge b c) by ix1 iix1 end a2
              ] end
        end
      end   
	end. 