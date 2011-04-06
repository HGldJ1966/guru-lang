Include "plus.g".
Include "minus.g".

Define mult :=
   fun mult(n m : nat) : nat.
   	match n return nat with
          Z => Z
	| S n' => (plus m (mult n' m))
   	end.
	
Define	multZ : Forall (n:nat).{ (mult n Z) = Z } :=
	induction (n:nat) by x1 x2 IH return { (mult n Z) = Z } with
	Z => hypjoin (mult n Z) Z by x1 end
	| S n' => hypjoin (mult n Z) Z by x1 [IH n'] end
	end.
	
Define mult_total : Forall (x y :nat).Exists(z:nat).{(mult x y) = z} :=
	induction(x:nat) by x1 x2 IH 
        return Forall(y:nat).Exists(z:nat).{(mult x y) = z} with
	Z => foralli(y:nat). existsi Z {(mult x y) = *}
		hypjoin (mult x y) Z by x1 end
	|S x' =>  
           foralli(y:nat).
             existse [IH x' y] foralli(z':nat)(u:{(mult x' y) = z'}).
	     existse [plus_total y z'] foralli(z:nat)(u':{(plus y z') = z}).
		existsi z {(mult x y) = *} 
		  hypjoin (mult x y) z by x1 u u' end
	end.

Total mult mult_total.

Define multS : Forall (m n : nat). { (mult m (S n)) = (plus m (mult m n)) } :=
	induction(m:nat) by x1 x2 IH 
        return Forall(n : nat). { (mult m (S n)) = (plus m (mult m n)) } with
          Z => foralli(n:nat).
                 hypjoin (mult m (S n)) (plus m (mult m n)) by x1 end
	| S m' => foralli(n:nat).
                  trans hypjoin (mult m (S n))
                                (plus (S n) (mult m' (S n))) by x1 end
                  trans cong (plus (S n) *) [IH m' n]
                  % (plus (S n) (plus m' (mult m' n)))
                  existse [mult_total m' n] 
                  foralli(z:nat)(u:{(mult m' n) = z}).
                     trans cong (plus (S n) (plus m' *)) u
                     trans symm [plus_assoc (S n) m' z]
                     trans cong (plus * z) trans [plusS_hop n m']
                                                 [plus_comm n (S m')]
                     trans [plus_assoc (S m') n z]
                     trans cong (plus * (plus n z)) symm x1
                     trans cong (plus m (plus n *)) symm u
                           cong (plus m *) 
                                 hypjoin (plus n (mult m' n)) (mult m n)
                                   by x1 end
	end. 

Define multOne : Forall(m:nat).{(mult m (S Z)) = m} :=
  foralli(m:nat). 
    trans [multS m Z]
    trans cong (plus m *) [multZ m]
          [plusZ m].

Define multOne2 : Forall(m:nat).{(mult (S Z) m) = m} :=
  foralli(m:nat). 
    trans join (mult (S Z) m) (plus m Z)
          [plusZ m].
          
          

Define mult_plus
   : Forall(x y z :nat).{(mult (plus x y) z) = (plus (mult x z) (mult y z))} :=
 induction (x:nat) by x1 x2 IH 
   return Forall(y z:nat).{(mult (plus x y) z) = 
                           (plus (mult x z) (mult y z))} with
   Z => foralli(y z : nat).
        hypjoin (mult (plus x y) z) (plus (mult x z) (mult y z)) by
           x1 end
 | S x' => foralli(y z : nat).
             trans hypjoin (mult (plus x y) z) (plus z (mult (plus x' y) z)) 
                     by x1 end
             trans cong (plus z *) [IH x' y z]
             existse [mult_total x' z] 
             foralli(x'z:nat)(ux'z:{(mult x' z) = x'z}).
               existse [mult_total y z] 
               foralli(yz:nat)(uyz:{(mult y z) = yz}).
                 trans hypjoin (plus z (plus (mult x' z) (mult y z)))
                               (plus z (plus x'z yz)) by ux'z uyz end
                 trans symm [plus_assoc z x'z yz]
                       hypjoin (plus (plus z x'z) yz)
                               (plus (mult x z) (mult y z)) by x1 ux'z uyz end
 end.


Define mult_comm : Forall(n m :nat).{(mult n m) = (mult m n)} :=
  induction (n:nat) by x1 x2 IH
  return Forall(m:nat).{(mult n m) = (mult m n)} with
	Z => foralli(m : nat). 
                hypjoin (mult n m) (mult m n) by x1 [multZ m] end
	| S n' => foralli(m : nat).
		trans hypjoin (mult n m) (plus m (mult n' m)) by x1 end
                trans cong (plus m *) [IH n' m]
                trans symm [multS m n']
                      cong (mult m *) symm x1
	end.	

Define mult_plus2 : Forall(x y z:nat). 
                      {(mult x (plus y z)) = (plus (mult x y) (mult x z))} :=
  foralli(x y z:nat). 
    trans [ mult_comm x terminates (plus y z) by plus_total ]
    trans [ mult_plus y z x]
    trans cong (plus * (mult z x)) [ mult_comm y x]
          cong (plus (mult x y) *) [ mult_comm z x].

Define mult_assoc : Forall(m n p: nat).{(mult (mult m n) p) = (mult m (mult n p))} :=
	induction(m:nat) by x1 x2 IH 
        return Forall(n p: nat).
                {(mult (mult m n) p) = (mult m (mult n p))} with
          Z => foralli(n p:nat).
                 hypjoin (mult (mult m n) p) (mult m (mult n p)) by x1 end
        | S m' => 
            foralli(n p:nat).
                %- (mult (mult (S m') n) p)
                   (mult (plus n (mult m' n)) p)
                   (plus (mult n p) (mult (mult m' n) p))
                   (plus (mult n p) (mult m' (mult n p)))
                   (plus (mult (S Z) (mult n p)) (mult m' (mult n p)))
                   (mult (plus (S Z) m') (mult n p))
                   (mult m (mult n p)) -%
                existse [mult_total m' n] 
                foralli(m'n:nat)(um'n:{(mult m' n) = m'n}).
                  trans hypjoin (mult (mult m n) p)
                                (mult (plus n m'n) p)
                        by x1 um'n end
                  trans [mult_plus n m'n p]
                  trans cong (plus (mult n p) *) 
                             trans cong (mult * p) symm um'n
                                   [IH m' n p]
                  existse [mult_total n p] 
                  foralli(np:nat)(unp:{(mult n p) = np}).
                  trans cong (plus * (mult m' *)) unp
                  trans cong (plus * (mult m' np)) 
                           symm [multOne2 np]
                  trans symm [mult_plus (S Z) m' np]
                  trans hypjoin (mult (plus (S Z) m') np)
                                (mult m np) by x1 end
                        cong (mult m *) symm unp
	end.
	
Define mult_switch
 : Forall(a b c d : nat).
   {(mult (mult a b) (mult c d)) = (mult (mult a c) (mult b d))} :=
  foralli(a b c d : nat).
    existse [mult_total c d] 
    foralli(cd:nat)(ucd:{(mult c d) = cd}).
    existse [mult_total b d] 
    foralli(bd:nat)(ubd:{(mult b d) = bd}).
      trans cong (mult (mult a b) *) ucd 
      trans [mult_assoc a b cd]
      trans cong (mult a (mult b *)) symm ucd
      trans cong (mult a *) symm [mult_assoc b c d]
      trans cong (mult a (mult * d)) [mult_comm b c]
      trans cong (mult a *) [mult_assoc c b d]
      trans cong (mult a (mult c *)) ubd
      trans symm [mult_assoc a c bd]
            cong (mult (mult a c) *) symm ubd.

Define mult_switch2
 : Forall(x y z : nat).{ (mult (mult x y) z) = (mult (mult x z) y) } :=
  foralli(x y z : nat).
    trans [mult_assoc x y z]
    trans cong (mult x *) [mult_comm y z]
          symm [mult_assoc x z y].


Define mult_not_zero : Forall(x y:nat)(u:{ x != Z })(v:{ y != Z }).{ (mult x y) != Z } :=
  induction(x:nat) by xp xt IHx return Forall(y:nat)(u:{ x != Z })(v:{ y != Z }).{ (mult x y) != Z } with
    Z =>
      foralli(y:nat)(u:{ x != Z })(v:{ y != Z }).
        contra trans xp
                     symm u
          { (mult x y) != Z }
  | S x' =>
      foralli(y:nat)(u:{ x != Z })(v:{ y != Z }).
        existse [mult_total x' y]
          foralli(m:nat)(mpf:{ (mult x' y) = m }).
            trans cong (mult * y) xp
            trans join (mult (S x') y)
                       (plus y (mult x' y))
            trans cong (plus y *) mpf
                  [plus_not_zero y m v]
  end.

Define mult_eq_Z : Forall(x y:nat)(u:{(mult (S x) y) = Z}). { y = Z } :=
  induction(x:nat) by ux ign IH 
  return Forall(y:nat)(u:{(mult (S x) y) = Z}). { y = Z } with
    Z => foralli(y:nat)(u:{(mult (S x) y) = Z}).
         symm trans symm u
              trans cong (mult (S *) y) ux
                 [multOne2 y]
  | S x' => foralli(y:nat)(u:{(mult (S x) y) = Z}).
            [plus_eq_Z1 y (mult (S x') y) 
              symm
                trans symm u
                trans cong (mult (S *) y) ux
                   join (mult (S (S x')) y) (plus y (mult (S x') y))]
  end.

Define mult_dist : Forall(x y z:nat).{ (mult x (plus y z)) = (plus (mult x y) (mult x z)) } :=
  foralli(x y z:nat).
    existse [plus_total y z]
      foralli(n:nat)(npf:{ (plus y z) = n }).
        symm trans cong (plus * (mult x z)) [mult_comm x y]
             trans cong (plus (mult y x) *) [mult_comm x z]
             trans symm [mult_plus y z x]
             trans cong (mult * x) npf
             trans [mult_comm n x]
                   cong (mult x *) symm npf.

Define mult_distr : Forall(x y z:nat).{ (mult (plus x y) z) = (plus (mult x z) (mult y z)) } :=
  foralli(x y z:nat).
    trans [mult_comm terminates (plus x y) by plus_total z]
    trans [mult_dist z x y]
    trans cong (plus * (mult z y))
               [mult_comm z x]
          cong (plus (mult x z) *)
               [mult_comm z y].

Define trusted mult_dist_minus : Forall(x y z:nat).
  { (mult x (minus y z)) = (minus (mult x y) (mult x z)) } :=
  truei.
  
Define mult_foil : Forall(a b c d:nat).{ (mult (plus a b) (plus c d)) = (plus (plus (plus (mult a c) (mult a d)) (mult b c)) (mult b d)) } :=
  foralli(a b c d:nat).
    trans [mult_dist terminates (plus a b) by plus_total c d]
    trans cong (plus * (mult (plus a b) d))
               trans [mult_comm (plus a b) c]
                     [mult_dist c a b]
    trans cong (plus (plus (mult c a) (mult c b)) *)
               trans [mult_comm (plus a b) d]
                     [mult_dist d a b]
    trans cong (plus (plus * (mult c b)) (plus (mult d a) (mult d b)))
               [mult_comm c a]
    trans cong (plus (plus (mult a c) *) (plus (mult d a) (mult d b)))
               [mult_comm c b]
    trans cong (plus (plus (mult a c) (mult b c)) (plus * (mult d b)))
               [mult_comm d a]
    trans cong (plus (plus (mult a c) (mult b c)) (plus (mult a d) *))
               [mult_comm d b]
    trans symm [plus_assoc (plus (mult a c) (mult b c))
                           (mult a d)
                           (mult b d)]
    trans cong (plus * (mult b d))
               [plus_assoc  (mult a c)
                            (mult b c)
                            (mult a d)]
    trans cong (plus (plus (mult a c) *) (mult b d))
               [plus_comm (mult b c)
                          (mult a d)]
          cong (plus * (mult b d))
               symm [plus_assoc (mult a c)
                                (mult a d)
                                (mult b c)].
  
Define mult_lt : Forall(x y z : nat)(u: { (lt y z) = tt}).
                 { (lt (mult (S x) y) (mult (S x) z)) = tt } :=
  foralli(x y z : nat)(u: { (lt y z) = tt}).
  [induction(x:nat) 
   return { (lt (mult (S x) y) (mult (S x) z)) = tt } with
     Z => trans cong (lt (mult (S *) y) (mult (S *) z)) x_eq
            hypjoin (lt (mult (S Z) y) (mult (S Z) z)) 
                    tt
            by x_eq [plusZ y] [plusZ z] u end
   | S x' => 
     trans cong (lt (mult (S *) y) (mult (S *) z)) x_eq
     trans join (lt (mult (S (S x')) y) (mult (S (S x')) z)) 
                (lt (plus y (mult (S x') y)) (plus z (mult (S x') z)))
           [plus_lt_both y z (mult (S x') y) (mult (S x') z) u [x_IH x']]
  end x].

Define mult_le : Forall(x y:nat)(u:{ y != Z }).{ (le x (mult x y)) = tt } :=
  foralli(x y:nat)(u:{ y != Z }).
    existse [not_zero_implies_S y u] foralli(y':nat)(v:{(S y') = y}).
    abbrev p1 =
      trans join (plus x (mult y' x)) (mult (S y') x)
      [mult_comm (S y') x] in
      
    symm trans symm [plus_implies_le x (mult y' x)]
    trans cong (le x *) p1
    cong (le x (mult x *)) v.

Define trusted mult_lt2 : Forall(x y : nat)(u1:{ x != Z })(u2: { (lt one y) = tt}).
  { (lt x (mult y x))  = tt } := truei.






