Include "nat.g".
Include "P.g".

Define plus :=
  fun plus(n m : nat) : nat.
    match n with
      Z => m
    | S n' => (S (plus n' m))
    end.

Define plusZ : Forall(n:nat). { (plus n Z) = n } :=
  induction(n:nat) return { (plus n Z) = n } with
    Z => trans cong (plus * Z) n_eq
         trans join (plus Z Z) Z
               symm n_eq
  | S n' => trans cong (plus * Z) n_eq
            trans join (plus (S n') Z) (S (plus n' Z))
            trans cong (S *) [n_IH n']
                  symm n_eq
  end.

Define plusS : Forall(n m : nat). { (plus n (S m)) = (S (plus n m))} :=
	induction (n:nat) return Forall(m:nat).{ (plus n (S m)) = (S (plus n m))} with
		Z => foralli(m : nat).
		     trans cong (plus * (S m)) n_eq
		     trans join (plus Z (S m)) (S (plus Z m))
		     cong (S (plus * m)) symm n_eq
		| S n' => foralli(m : nat).
			trans cong (plus * (S m)) n_eq
			trans join (plus (S n') (S m)) (S (plus n' (S m)))
			trans cong (S *) [n_IH n' m]
			trans join (S (S (plus n' m))) (S (plus (S n') m))
			cong (S (plus * m)) symm n_eq
	end.

Define plusS_hop : Forall(n m : nat). {(plus (S n) m) = (plus n (S m))} :=
  foralli(n m:nat).
    hypjoin (plus (S n) m) (plus n (S m)) by [plusS n m] end.

Define plus_comm : Forall (n m :nat). { (plus n m) = (plus m n) } :=
induction (n : nat) return Forall(m : nat).{ (plus n m) = (plus m n) } with
  Z => foralli(m : nat).
       trans cong (plus * m) n_eq
       trans join (plus Z m) m
       trans cong * symm [plusZ m]
             cong (plus m *) symm n_eq
| S n' => foralli(m : nat).
          trans cong (plus * m) n_eq
          trans join (plus (S n') m) (S (plus n' m))
          trans cong (S *)  [n_IH n' m]
          trans cong * symm [plusS m n']
                cong (plus m *) symm n_eq
end.

Define plus_assoc : Forall(x y z:nat). { (plus (plus x y) z) = (plus x (plus y z)) } :=
  induction(x:nat) by x1 x2 IH return
                   Forall(y z : nat).
                     { (plus (plus x y) z) = (plus x (plus y z)) }
  with
    Z => foralli(y z : nat).
         trans cong (plus (plus * y) z) x1
         trans join (plus (plus Z y) z) (plus y z)
         trans symm join (plus Z (plus y z)) (plus y z)
               cong (plus * (plus y z)) symm x1
  | S x' => foralli(y z : nat).
            trans cong (plus (plus * y) z) x1
            trans join (plus (plus (S x') y) z) (S (plus (plus x' y) z))
            trans cong (S *) [IH x' y z]
            trans symm join (plus (S x') (plus y z)) (S (plus x' (plus y z)))
                  cong (plus * (plus y z)) symm x1
end.

Define plus_total : Forall ( x  y : nat). Exists(z:nat).{(plus x y) = z} :=
	induction (x : nat) return Forall(y:nat). Exists(z:nat).{(plus x y) = z} with
	Z => foralli(y:nat).
             existsi y {(plus x y) = *}
		trans cong (plus * y) x_eq
                      join (plus Z y) y
	| S x' => foralli(y:nat).
		existse [x_IH x' y] foralli(z':nat)(u:{(plus x' y) = z'}). 
		existsi (S z') {(plus x y) = *}  
                  trans cong (plus * y) x_eq
                  trans join (plus (S x') y) (S (plus x' y))
                        cong (S *) u
	end. 

Total plus plus_total.

Define plus_not_zero : Forall(n m : nat)(a:{n != Z}).{(plus n m) != Z} :=
	induction(n:nat) by x1 x2 IH return Forall(m:nat)(a:{n != Z}).{(plus n m) != Z}  with
	Z => foralli(m:nat).
		foralli(a:{n != Z}).
		contra trans symm x1 a
		{(plus n m) != Z}
	|S n' => foralli(m:nat).
		foralli(a:{n != Z}).
		trans cong (plus * m) x1
		trans join (plus (S n') m) (S (plus n' m))
		existse [plus_total n' m] foralli(q:nat)(u:{(plus n' m) = q}).
		trans cong (S *) u
		clash (S q) Z
	end.

%Set "debug_terminates".

Define plus_eq_Z1 : Forall(n m: nat)(u:{(plus n m) = Z}).{n = Z} :=
  induction(n:nat) by un ign IH 
  return Forall(m: nat)(u:{(plus n m) = Z}).{n = Z} with
    Z => foralli(m: nat)(u:{(plus n m) = Z}). un
  | S n' => foralli(m: nat)(u:{(plus n m) = Z}).
            contra
              trans
                trans symm u hypjoin (plus n m) (S (plus n' m)) by un end
                clash (S terminates (plus n' m) by plus_total) Z
              { n = Z }
  end.

Define plus_eq_Z2 : Forall(n m: nat)(u:{(plus n m) = Z}).{m = Z} :=
  foralli(n m: nat)(u:{(plus n m) = Z}).
    hypjoin m Z 
    by u [plus_eq_Z1 n m u] end.

Define P_add : Forall(x:nat)(u:{x != Z}).{(plus (P x) (P x)) = (P (P (plus x x)))} :=
	induction(x:nat) by x1 x2 IH return Forall(u:{x != Z}). {(plus (P x) (P x)) = (P (P (plus x x)))} with
	Z => foralli(u:{x != Z}).
		 contra trans symm x1 u
		 	{(plus (P x) (P x)) = (P (P (plus x x)))}
	| S x' => foralli(u:{x != Z}).
		trans cong (plus (P *) (P *)) x1
		trans cong (plus * *) [PS_lemma x']
		existse [plus_total x' x'] foralli(z:nat)(v:{(plus x' x') = z}).
		trans v
		trans symm [PS_lemma z]
		trans cong (P *) symm [PS_lemma (S z)]
		trans cong (P (P (S (S *)))) symm v
		trans cong (P (P (S *))) symm [plusS x' x']
		trans join (P (P (S(plus x' (S x'))))) (P (P (plus (S x') (S x'))))
		cong (P (P (plus * *))) symm x1
	end.

Define S_plus_eq_S_implies_plus : Forall(a b c:nat)(u:{(plus (S a) b) = (S c)}).{(plus a b) = c} :=
	foralli(a b c:nat)(u:{(plus (S a) b) = (S c)}).
		existse [plus_total a b] foralli(d:nat)(d':{(plus a b) = d}).
		symm trans symm inj (S *) trans cong (S *) symm d' trans join (S (plus a b)) (plus (S a) b) u
		symm d'.

Define S_plus_eq_implies_plus_eq_P: Forall(a b c: nat)(u:{(plus (S a) b) = c}).{(plus a b) = (P c)} :=
	foralli(a b c: nat)(u:{(plus (S a) b) = c}).
	existse [plus_total a b] foralli(d:nat)(d':{(plus a b) = d}).
	symm trans symm [S_to_P d c symm trans symm u trans join (plus (S a) b) (S (plus a b)) cong (S *) d']
	symm d'.

Define plus_implies_lt : Forall(a b c:nat)(u:{b != Z})(v:{(plus a b) = c }).{(lt a c) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b c:nat)(u:{b != Z})(v:{(plus a b) = c }).{(lt a c) = tt} with
	Z=>foralli(b c:nat)(u:{b != Z})(v:{(plus a b) = c }).
		trans cong (lt * c) x1
		[not_zero_implies_lt c trans symm v trans cong (plus * b) x1 trans [plus_comm Z b] [plus_not_zero b Z u]]
	| S a' => foralli(b c:nat)(u:{b != Z})(v:{(plus a b) = c }).
		[induction(d:nat) by y1 y2 IH2 return Forall(q:{d = c}).{(lt a c) = tt}  with
			Z=> foralli(q:{d = c}).
				contra trans symm y1 trans q trans symm v trans cong (plus * b) x1 trans [plus_comm (S a') b] [plus_not_zero b (S a') u]
					{(lt a c) = tt}
			|S d' => foralli(q:{d = c}).
				symm trans symm [IH a' b d' u [S_plus_eq_S_implies_plus a' b d' trans symm cong (plus * b) x1 trans v trans symm q y1]]
				 trans symm [S_lt_S a' d' ]
				trans cong (lt * (S d')) symm x1
				trans cong (lt a *) symm y1
				cong (lt a *) q
		end c join c c]
	end.

Define plus_implies_P_eq_P : Forall(a b c : nat)(u:{b != Z})(v:{(plus a b) = c}).{(plus a (P b)) = (P c)} :=
	foralli(a b c : nat)(u:{b != Z})(v:{(plus a b) = c}).
	existse [P_total b u] foralli(d:nat)(d':{(P b) = d}).
	symm trans symm [S_plus_eq_implies_plus_eq_P d a c symm trans symm v trans cong (plus a *) symm [PS_lemma2 b u] trans cong (plus a (S *)) d' [plus_comm a (S d)]]
	trans [plus_comm d a]
	cong (plus a *) symm d'.

Define plus_implies_S_eq_S : Forall(a b c : nat)(v:{(plus a b) = c}).{(plus (S a) b) = (S c)} :=
	foralli(a b c : nat)(v:{(plus a b) = c}). trans join (plus (S a) b) (S (plus a b)) cong (S *) v.


Define lt_implies_plus : Forall(a:nat)(b:nat)(u:{(lt a b) = tt}).Exists(c:nat)(v:{ c != Z}).{(plus a c) = b} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(u:{(lt a b) = tt}).Exists(c:nat)(v:{ c != Z}).{(plus a c) = b} with
	Z => foralli(b:nat).
		foralli(u:{(lt a b) = tt}).
		existsi b Exists(v:{ * != Z}).{(plus a *) = b}
		existsi [lt_implies_not_zero a b u] {(plus a b) = b}
		trans cong (plus * b) x1
		join (plus Z b) b
	| S a' => foralli(b:nat).
		foralli(u:{(lt a b) = tt}).
		[induction(d:nat) by y1 y2 IH2 return Forall(l:{d=b}).Exists(q:nat)(l:{q != Z}).{(plus a q) = d} with
		Z => foralli(l:{d=b}).
			contra trans symm y1 trans l [lt_implies_not_zero a b u]
				Exists(q:nat)(v:{q != Z}).{(plus a q) = d}
		|S d' =>  foralli(l:{d=b}).
			 existse [IH a' d' trans symm [S_lt_S a' d'] trans cong (lt * (S d')) symm x1 trans cong (lt a *) symm y1 trans cong (lt a *) l u]
			 	foralli(q:nat)(x:{ q != Z})(y:{(plus a' q) = d'}).
			existsi q Exists(v:{ * != Z}).{(plus a *) = d}
			existsi x {(plus a q) = d}
			trans cong (plus * q) x1 trans [plus_implies_S_eq_S a' q d' y] symm y1

		end b join b b]
	end.

Define plus_inj2 : Forall(a b c:nat)(u:{ (plus a b) = (plus a c) }).{ b = c } :=
  induction(a:nat) by ap at IHa return Forall(b c:nat)(u:{ (plus a b) = (plus a c) }).{ b = c } with
    Z =>
      foralli(b c:nat)(u:{ (plus a b) = (plus a c) }).
        trans join b (plus Z b)
        trans cong (plus * b) symm ap
        trans u
        trans cong (plus * c) ap
              join (plus Z c) c
  | S a' =>
      foralli(b c:nat)(u:{ (plus a b) = (plus a c) }).
        abbrev u' = inj (S *)
                        trans join (S (plus a' b))
                                   (plus (S a') b)
                        trans cong (plus * b) symm ap
                        trans u
                        trans cong (plus * c) ap
                              join (plus (S a') c)
                                   (S (plus a' c)) in
        [IHa a' b c u']
  end.

Define plus_lt : Forall(x y z:nat)(u:{(lt y z) = tt}).
                   { (lt (plus x y) (plus x z)) = tt} :=
  induction(x:nat) by ux vx IH 
    return Forall(y z:nat)(u:{(lt y z) = tt}).
            { (lt (plus x y) (plus x z)) = tt}
    with
    Z => foralli(y z:nat)(u:{(lt y z) = tt}).
           trans cong (lt (plus * y) (plus * z)) ux
           trans join (lt (plus Z y) (plus Z z)) (lt y z)
                 u
  | S x' => foralli(y z:nat)(u:{(lt y z) = tt}).
              trans cong (lt (plus * y) (plus * z)) ux
              trans join (lt (plus (S x') y) (plus (S x') z))
                         (lt (plus x' y) (plus x' z))
                    [IH x' y z u]
  end.

Define plus_lt2 : Forall(x y z:nat)(u:{(lt x y) = tt}).
                   { (lt (plus x z) (plus y z)) = tt} :=
  foralli(x y z:nat)(u:{(lt x y) = tt}).
    symm
    trans symm [plus_lt z x y u]
    trans cong (lt * (plus z y)) [plus_comm z x]
          cong (lt (plus x z) *) [plus_comm z y].
  
Define plus_lt_both 
  : Forall(a b x y:nat)(u1:{(lt a b) = tt})(u2:{(lt x y) = tt}).
     { (lt (plus a x) (plus b y)) = tt} :=
  foralli(a b x y:nat)(u1:{(lt a b) = tt})(u2:{(lt x y) = tt}).
    [lt_trans terminates (plus a x) by plus_total
              terminates (plus a y) by plus_total
              terminates (plus b y) by plus_total
      [plus_lt a x y u2]  
      [plus_lt2 a b y u1]].

Define plus_le : Forall(x y z:nat)(u:{(le y z) = tt}).
                       { (le (plus x y) (plus x z)) = tt} :=
  foralli(x y z:nat)(u:{(le y z) = tt}).
    trans join (le (plus x y) (plus x z))
               (or (lt (plus x y) (plus x z)) 
                   (eqnat (plus x y) (plus x z)))
      existse [lt_total y z]
      induction(q:bool) by uq vq nIH 
        return Forall(uq:{(lt y z) = q}).{ (or (lt (plus x y) (plus x z)) 
                                               (eqnat (plus x y) (plus x z)))
                                          = tt }
        with
        ff => foralli(uq2:{(lt y z) = q}).
                trans cong (or (lt (plus x *) (plus x z))
                               (eqnat (plus x *) (plus x z)))
                        [eqnatEq y z 
                          symm
                          trans symm u
                          trans join (le y z)
                                     (or (lt y z) (eqnat y z))
                          trans cong (or * (eqnat y z))
                                  trans uq2 uq
                                join (or ff (eqnat y z))
                                     (eqnat y z)]
                existse [plus_total x z]
                foralli(q:nat)(u:{(plus x z) = q}).
                  trans cong (or (lt (plus x z) (plus x z)) *)
                          trans cong (eqnat * *) u [eqnat_refl q]  
                  trans cong (or * tt)
                          trans cong (lt * *) u [x_lt_x q]
                        join (or ff tt) tt
      | tt => foralli(uq2:{(lt y z) = q}).
                 trans cong (or * (eqnat (plus x y) (plus x z)))
                         [plus_lt x y z trans uq2 uq]
                 join (or tt (eqnat (plus x y) (plus x z))) tt
      end.

Define plus_transform_1 : Forall(a b c d:nat).{ (plus (plus a c) (plus b d)) = (plus (plus (plus a b) c) d) } :=
  foralli(a b c d:nat).
    trans cong (plus * (plus b d))
               [plus_comm a c]
    trans [plus_assoc c a terminates (plus b d) by plus_total]
    trans [plus_comm c terminates (plus a terminates (plus b d) by plus_total) by plus_total]
    trans cong (plus * c)
               symm [plus_assoc a b d]
    trans [plus_assoc terminates (plus a b) by plus_total d c]
    trans cong (plus (plus a b) *)
               [plus_comm d c]
          symm [plus_assoc terminates (plus a b) by plus_total c d].

Define lt_Splus : Forall(a b:nat). { (lt a (S (plus a b))) = tt } :=
  foralli(a b:nat).
    trans symm cong (lt a *) [plusS a b]
     [plus_implies_lt a (S b) terminates (plus a (S b)) by plus_total
        clash (S b) Z
        join (plus a (S b)) (plus a (S b))].
      
Define lt_Splus2 : Forall(a b:nat). { (lt b (S (plus a b))) = tt } :=
  foralli(a b:nat).
    trans cong (lt b (S *)) [plus_comm a b]
          [lt_Splus b a].
      
Define plus_implies_le : Forall(a b:nat). { (le a (plus a b)) = tt } :=
  foralli(a b:nat).
    case b with
      Z => hypjoin (le a (plus a b)) tt
           by b_eq [x_lt_x a] [plusZ a] [eqnat_refl a] end
    | S b' => 
      hypjoin (le a (plus a b)) tt
      by b_eq [plus_implies_lt a (S b') 
                  terminates (plus a (S b')) by plus_total
                  clash (S b') Z
                  join (plus a (S b')) (plus a (S b'))]
      end
    end.