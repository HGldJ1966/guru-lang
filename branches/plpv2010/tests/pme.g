Include "../lib/nat.g".
Include "../lib/plus.g".
Include "../lib/mult.g".
Set "print_parsed".

Inductive pme : type :=
	  pluse : Fun(x y : pme).pme
	| multe : Fun(x y : pme).pme
	| nate : Fun(n : nat).pme.

Define interp : Fun (x:pme).nat :=
	fun interp(x:pme) : nat.
	match x return nat with
		pluse e1 e2 => 	(plus (interp e1)(interp e2))
		| multe e1 e2 =>	(mult (interp e1)(interp e2))		
		| nate n => 		n
	end.




%-
Define simplify_mhelper : Fun (x y : pme).pme :=
	fun simplify_mhelper (x y : pme) : pme.
	match x return pme with
		  pluse e1 e2 =>	(pluse (simplify_mhelper e1 y)(simplify_mhelper e2 y))
		| multe e1 e2 =>	(simplify_mhelper e1 (simplify_mhelper e2 y))
		| nate n => 		(multe (nate n) y)
	end.

Define simplify_phelper : Fun (x y : pme).pme :=
	fun simplify_phelper (x y : pme) : pme.
	match x return pme with
		  pluse e1 e2 =>	(simplify_phelper e1 (simplify_phelper e2 y))
		| multe e1 e2 =>	(pluse (simplify_mhelper (multe e1 e2) (nate (S Z))) y)
		| nate n => 		(pluse (nate n) y)
	end.
	
Define simplify : Fun (x:pme).pme :=
	fun simplify(x:pme) : pme.
	match x return pme with
		  pluse e1 e2 =>	(simplify_phelper (pluse e1 e2) (nate Z))
		| multe e1 e2 =>	(simplify_mhelper (multe e1 e2) (nate (S Z)))
		| nate n => 		(nate n)
	end.

Define result1 := (interp (pluse (pluse (nate one) (nate two)) (pluse (nate three) (nate four)))).
% Interpret result1.
Define result2 := (simplify (pluse (pluse (nate one) (nate two)) (pluse (nate three) (nate four)))).
% Interpret result2.
Define result3 := (interp result2).
% Interpret result3.
Define result4 := (interp (simplify result2)).
% Interpret result4.

Define formula1 := (multe (pluse (nate one) (nate two)) (nate three)).
Define formula2 := (multe (pluse (nate four) (nate five)) (nate six)).
Define result5 := (simplify formula1). Interpret result5.
Define total := (multe (pluse formula1 formula2) (nate seven)).
Define result6 := (simplify total). Interpret result6.

Define total1 := (multe (multe (nate one)(nate two)) (pluse (nate three)(nate four))).
Define result7 := (simplify total1). Interpret result7.
Define total2 := (multe (pluse (nate one)(nate two)) (pluse (nate three)(nate four))).
Define result8 := (simplify total2). Interpret result8.
Define result9 := (interp result8). Interpret result9.

Define interpTot : Forall(x:pme).Exists(z:nat).{ (interp x) = z } :=
	induction (x:pme) by x1 x2 IHx return Exists(z:nat).{ (interp x) = z } with
		pluse e1 e2 =>
			existsi (plus (interp e1)(interp e2)) { (interp x) = * }
			trans cong (interp *) x1
			join (interp (pluse e1 e2)) (plus (interp e1)(interp e2))
		| multe e1 e2 =>
			existsi (mult (interp e1)(interp e2)) { (interp x) = * }
			trans cong (interp *) x1
			join (interp (multe e1 e2)) (mult (interp e1)(interp e2))
		| nate n => 
			existsi n { (interp x) = * }
			trans cong (interp *) x1
			join (interp (nate n)) n
	end.


Define simplify_phelperTot : Forall(x y : pme).Exists(z:pme).{ (simplify_phelper x y) = z } :=
	induction (x:pme) by x1 x2 IHx return Forall(y:pme).Exists(z:pme).{ (simplify_phelper x y) = z } with
		pluse e1 e2 =>
			foralli(y:pme).
			existsi (simplify_phelper e1 (simplify_phelper e2 y)) { (simplify_phelper x y) = * }
			trans cong (simplify_phelper * y) x1
			join (simplify_phelper (pluse e1 e2) y) (simplify_phelper e1 (simplify_phelper e2 y))
		| multe e1 e2 =>
			foralli(y:pme).
			existsi (pluse (simplify_mhelper (multe e1 e2) (nate (S Z))) y) { (simplify_phelper x y) = * }
			trans cong (simplify_phelper * y) x1
			join (simplify_phelper (multe e1 e2) y) (pluse (simplify_mhelper (multe e1 e2) (nate (S Z))) y)
		| nate n => 
			foralli(y:pme).
			existsi (pluse (nate n) y) { (simplify_phelper x y) = * }
			trans cong (simplify_phelper * y) x1			
			join (simplify_phelper (nate n) y) (pluse (nate n) y)			
	end.

Define simplify_mhelperTot : Forall(x y : pme).Exists(z:pme).{ (simplify_mhelper x y) = z } :=
	induction (x:pme) by x1 x2 IHx return Forall(y:pme).Exists(z:pme).{ (simplify_mhelper x y) = z } with
		pluse e1 e2 =>
			foralli(y:pme).
			existsi (pluse (simplify_mhelper e1 y)(simplify_mhelper e2 y)) { (simplify_mhelper x y) = * }
			trans cong (simplify_mhelper * y) x1
			join (simplify_mhelper (pluse e1 e2) y) (pluse (simplify_mhelper e1 y)(simplify_mhelper e2 y))
		| multe e1 e2 =>
			foralli(y:pme).
			existsi (simplify_mhelper e1 (simplify_mhelper e2 y)) { (simplify_mhelper x y) = * }
			trans cong (simplify_mhelper * y) x1
			join (simplify_mhelper (multe e1 e2) y) (simplify_mhelper e1 (simplify_mhelper e2 y))
		| nate n => 
			foralli(y:pme).
			existsi (multe (nate n) y) { (simplify_mhelper x y) = * }
			trans cong (simplify_mhelper * y) x1			
			join (simplify_mhelper (nate n) y) (multe (nate n) y)			
	end.
	
Define pluse_Z : Forall(x:pme).{ (interp (pluse x (nate Z))) = (interp x) } :=
	induction (x:pme) by x1 x2 IHx return { (interp (pluse x (nate Z))) = (interp x) } with
		pluse e1 e2 =>
			trans cong (interp (pluse * (nate Z))) x1
			trans join (interp (pluse (pluse e1 e2) (nate Z)))
				(plus (plus (interp e1)(interp e2)) Z)
			existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [plus_total e2i e1i] foralli(pt:nat) (ptu:{ (plus e1i e2i) = pt }).
		  	trans cong (plus (plus * (interp e2)) Z) e1iu
		  	trans cong (plus (plus e1i *) Z) e2iu
		  	trans cong (plus * Z) ptu
		  	trans [plusZ pt]
		  	trans symm ptu
		  	trans cong (plus * e2i) symm e1iu
		  	trans cong (plus (interp e1) *) symm e2iu
		  	trans join (plus (interp e1) (interp e2)) (interp (pluse e1 e2))
		  	cong (interp *) symm x1
		| multe e1 e2 =>
			trans cong (interp (pluse * (nate Z))) x1
			trans join (interp (pluse (multe e1 e2) (nate Z)))
				(plus (mult (interp e1)(interp e2)) Z)
			existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [mult_total e1i e2i] foralli(mt:nat) (mtu:{ (mult e1i e2i) = mt }).
		  	trans cong (plus (mult * (interp e2)) Z) e1iu
		  	trans cong (plus (mult e1i *) Z) e2iu
		  	trans cong (plus * Z) mtu
		  	trans [plusZ mt]
		  	trans symm mtu
		  	trans cong (mult * e2i) symm e1iu
		  	trans cong (mult (interp e1) *) symm e2iu
		  	trans join (mult (interp e1) (interp e2)) (interp (multe e1 e2))
		  	cong (interp *) symm x1	
		| nate n =>
			trans cong (interp (pluse * (nate Z))) x1
			trans join (interp (pluse (nate n) (nate Z))) (plus n Z)
			trans [plusZ n]
			trans join n (interp (nate n))
			cong (interp *) symm x1		
	end.

Define multe_one : Forall(x:pme).{ (interp (multe x (nate (S Z)))) = (interp x) } :=
	induction (x:pme) by x1 x2 IHx return { (interp (multe x (nate (S Z)))) = (interp x) } with
		pluse e1 e2 =>
			trans cong (interp (multe * (nate (S Z)))) x1
			trans join (interp (multe (pluse e1 e2) (nate (S Z))))
				(mult (plus (interp e1)(interp e2)) (S Z))
			existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [plus_total e2i e1i] foralli(pt:nat) (ptu:{ (plus e1i e2i) = pt }).
		  	trans cong (mult (plus * (interp e2)) (S Z)) e1iu
		  	trans cong (mult (plus e1i *) (S Z)) e2iu
		  	trans cong (mult * (S Z)) ptu
		  	trans [mult_by_one pt]
		  	trans symm ptu
		  	trans cong (plus * e2i) symm e1iu
		  	trans cong (plus (interp e1) *) symm e2iu
		  	trans join (plus (interp e1) (interp e2)) (interp (pluse e1 e2))
		  	cong (interp *) symm x1
		| multe e1 e2 =>
			trans cong (interp (multe * (nate (S Z)))) x1
			trans join (interp (multe (multe e1 e2) (nate (S Z))))
				(mult (mult (interp e1)(interp e2)) (S Z))
			existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [mult_total e1i e2i] foralli(mt:nat) (mtu:{ (mult e1i e2i) = mt }).
		  	trans cong (mult (mult * (interp e2)) (S Z)) e1iu
		  	trans cong (mult (mult e1i *) (S Z)) e2iu
		  	trans cong (mult * (S Z)) mtu
		  	trans [mult_by_one mt]
		  	trans symm mtu
		  	trans cong (mult * e2i) symm e1iu
		  	trans cong (mult (interp e1) *) symm e2iu
		  	trans join (mult (interp e1) (interp e2)) (interp (multe e1 e2))
		  	cong (interp *) symm x1	
		| nate n =>
			trans cong (interp (multe * (nate (S Z)))) x1
			trans join (interp (multe (nate n) (nate (S Z)))) (mult n (S Z))
			trans [mult_by_one n]
			trans join n (interp (nate n))
			cong (interp *) symm x1		
	end.

Define simp_multe_lemma : Forall (x y : pme).{ (interp (simplify_mhelper x y)) = (interp (multe x y)) } :=
	induction (x:pme) by x1 x2 IHx return Forall(y:pme).{ (interp (simplify_mhelper x y)) = (interp (multe x y)) } with
		  pluse e1 e2 =>
		  	foralli(y:pme).
			trans cong (interp (simplify_mhelper * y)) x1
			trans join (interp (simplify_mhelper (pluse e1 e2) y)) 
				(plus (interp (simplify_mhelper e1 y)) (interp (simplify_mhelper e2 y)))
			trans cong (plus * (interp (simplify_mhelper e2 y))) [IHx e1 y]
			trans cong (plus (interp (multe e1 y)) *) [IHx e2 y]
			trans join (plus (interp (multe e1 y)) (interp (multe e2 y)))
				(plus (mult (interp e1)(interp y)) (mult (interp e2)(interp y)))			
			existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [interpTot y] foralli(yi:nat) (yiu:{ (interp y) = yi }).		  	
		  	trans cong (plus (mult * (interp y)) (mult (interp e2)(interp y))) e1iu
		  	trans cong (plus (mult e1i (interp y)) (mult * (interp y))) e2iu
		  	trans cong (plus (mult e1i *) (mult e2i *)) yiu
		  	trans symm [mult_dist_2 yi e1i e2i]		  	
		  	trans cong (mult (plus * e2i) yi) symm e1iu
		  	trans cong (mult (plus (interp e1) *) yi) symm e2iu
		  	trans cong (mult (plus (interp e1) (interp e2)) *) symm yiu
		  	trans join (mult (plus (interp e1) (interp e2)) (interp y))		  		
		  		(interp (multe (pluse e1 e2) y))
		  	cong (interp (multe * y)) symm x1
		| multe e1 e2 =>
		  	foralli(y:pme).
		  	trans cong (interp (simplify_mhelper * y)) x1
		  	trans join (interp (simplify_mhelper (multe e1 e2) y))
		  		(interp (simplify_mhelper e1 (simplify_mhelper e2 y)))
		  	existse [simplify_mhelperTot e2 y] foralli(z:pme) (u:{ (simplify_mhelper e2 y) = z }).
		  	trans cong (interp (simplify_mhelper e1 *)) u
		  	trans cong * [IHx e1 z]
		  	trans cong (interp (multe e1 *)) symm u		  	
		  	trans join (interp (multe e1 (simplify_mhelper e2 y)))
		  		(mult (interp e1) (interp (simplify_mhelper e2 y)))
		  	trans cong (mult (interp e1) *) [IHx e2 y]
		  	trans join (mult (interp e1) (interp (multe e2 y)))
		  		(mult (interp e1) (mult (interp e2) (interp y)))
		  	existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [interpTot y] foralli(yi:nat) (yiu:{ (interp y) = yi }).
		  	trans cong (mult * (mult (interp e2) (interp y))) e1iu
		  	trans cong (mult e1i (mult * (interp y))) e2iu
		  	trans cong (mult e1i (mult e2i *)) yiu
		  	trans symm [mult_assoc e1i e2i yi]
		  	trans cong (mult (mult * e2i) yi) symm e1iu
		  	trans cong (mult (mult (interp e1) *) yi) symm e2iu
		  	trans cong (mult (mult (interp e1) (interp e2)) *) symm yiu
		  	trans join (mult (mult (interp e1) (interp e2)) (interp y))
		  		(interp (multe (multe e1 e2) y))
		  	cong (interp (multe * y)) symm x1		  				  	
		| nate n => 
			foralli(y:pme).
			trans cong (interp (simplify_mhelper * y)) x1
			trans join (interp (simplify_mhelper (nate n) y)) 
				(interp (multe (nate n) y))
			cong (interp (multe * y)) symm x1			
	end.

Define simp_pluse_lemma : Forall (x y : pme).{ (interp (simplify_phelper x y)) = (interp (pluse x y)) } :=
	induction (x:pme) by x1 x2 IHx return Forall(y:pme).{ (interp (simplify_phelper x y)) = (interp (pluse x y)) } with
		  pluse e1 e2 =>
		  	foralli(y:pme).
		  	trans cong (interp (simplify_phelper * y)) x1
		  	trans join (interp (simplify_phelper (pluse e1 e2) y))
		  		(interp (simplify_phelper e1 (simplify_phelper e2 y)))
		  	existse [simplify_phelperTot e2 y] foralli(z:pme) (u:{ (simplify_phelper e2 y) = z }).
		  	trans cong (interp (simplify_phelper e1 *)) u
		  	trans cong * [IHx e1 z]
		  	trans cong (interp (pluse e1 *)) symm u		  	
		  	trans join (interp (pluse e1 (simplify_phelper e2 y)))
		  		(plus (interp e1) (interp (simplify_phelper e2 y)))
		  	trans cong (plus (interp e1) *) [IHx e2 y]
		  	trans join (plus (interp e1) (interp (pluse e2 y)))
		  		(plus (interp e1) (plus (interp e2) (interp y)))
		  	existse [interpTot e1] foralli(e1i:nat) (e1iu:{ (interp e1) = e1i }).
		  	existse [interpTot e2] foralli(e2i:nat) (e2iu:{ (interp e2) = e2i }).
		  	existse [interpTot y] foralli(yi:nat) (yiu:{ (interp y) = yi }).
		  	trans cong (plus * (plus (interp e2) (interp y))) e1iu
		  	trans cong (plus e1i (plus * (interp y))) e2iu
		  	trans cong (plus e1i (plus e2i *)) yiu
		  	trans symm [plus_assoc e1i e2i yi]
		  	trans cong (plus (plus * e2i) yi) symm e1iu
		  	trans cong (plus (plus (interp e1) *) yi) symm e2iu
		  	trans cong (plus (plus (interp e1) (interp e2)) *) symm yiu
		  	trans join (plus (plus (interp e1) (interp e2)) (interp y))
		  		(interp (pluse (pluse e1 e2) y))
		  	cong (interp (pluse * y)) symm x1		  				  	
		| multe e1 e2 =>
			foralli(y:pme).
			trans cong (interp (simplify_phelper * y)) x1
			trans join (interp (simplify_phelper (multe e1 e2) y))
				(plus (interp (simplify_mhelper (multe e1 e2) (nate (S Z)))) (interp y))
			trans cong (plus * (interp y)) [simp_multe_lemma (multe e1 e2) (nate (S Z))]			
			trans cong (plus * (interp y)) [multe_one (multe e1 e2)]
			trans join (plus (interp (multe e1 e2)) (interp y))
				(interp (pluse (multe e1 e2) y))
			cong (interp (pluse * y)) symm x1
		| nate n => 
			foralli(y:pme).
			trans cong (interp (simplify_phelper * y)) x1
			trans join (interp (simplify_phelper (nate n) y)) 
				(interp (pluse (nate n) y))
			cong (interp (pluse * y)) symm x1			
	end.

Define const_simplify : Forall(x:pme).{ (interp (simplify x)) = (interp x) } :=
	induction (x:pme) by x1 x2 IHx return { (interp (simplify x)) = (interp x) } with
		  pluse e1 e2 =>
		  	trans cong (interp (simplify *)) x1
		  	trans join (interp (simplify (pluse e1 e2)))
		  		(interp (simplify_phelper e1 (simplify_phelper e2 (nate Z))))
		  	existse [simplify_phelperTot e2 (nate Z)] foralli(spt:pme) (sptu:{(simplify_phelper e2 (nate Z))=spt}).
		  	trans cong (interp (simplify_phelper e1 *)) sptu
		  	trans [simp_pluse_lemma e1 spt]
		  	trans join (interp (pluse e1 spt))
		  		(plus (interp e1) (interp spt))
		  	trans cong (plus (interp e1) (interp *)) symm sptu		  	
		  	trans cong (plus (interp e1) *) [simp_pluse_lemma e2 (nate Z)]		  	
		  	trans join (plus (interp e1)(interp (pluse e2 (nate Z))))
		  		(plus (interp e1)(interp (pluse e2 (nate Z))))
		  	trans cong (plus (interp e1) *) [pluse_Z e2]
		  	trans join (plus (interp e1)(interp e2)) (interp (pluse e1 e2))
		  	cong (interp *) symm x1		  	
		| multe e1 e2 =>	
		  	trans cong (interp (simplify *)) x1
		  	trans join (interp (simplify (multe e1 e2)))
		  		(interp (simplify_mhelper e1 (simplify_mhelper e2 (nate (S Z)))))
		  	existse [simplify_mhelperTot e2 (nate (S Z))] 
		  		foralli(smt:pme) (smtu:{(simplify_mhelper e2 (nate (S Z)))=smt}).
		  	trans cong (interp (simplify_mhelper e1 *)) smtu
		  	trans [simp_multe_lemma e1 smt]
		  	trans join (interp (multe e1 smt))
		  		(mult (interp e1) (interp smt))
		  	trans cong (mult (interp e1) (interp *)) symm smtu		  	
		  	trans cong (mult (interp e1) *) [simp_multe_lemma e2 (nate (S Z))]		  	
		  	trans join (mult (interp e1)(interp (multe e2 (nate (S Z)))))
		  		(interp (multe e1 e2))
		  	cong (interp *) symm x1	
		| nate n =>
			trans cong (interp (simplify *)) x1
			trans join (interp (simplify (nate n)))
				(interp (nate n))
			cong (interp *) symm x1		
	end.

	


-%
