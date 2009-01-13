Include "../lib/nat.g".
Include "../lib/pair.g".
Include "../lib/mult.g".

%Set "print_parsed".

Define rat : type := <pair nat nat>.
Define numer := fun(p:rat).(fst nat nat p).
Define denom := fun(p:rat).(snd nat nat p).

Define reduce_one : Fun(x:rat).rat :=
	fun reduce_one(x:rat) : rat.
	match (eqnat (numer x) (denom x)) by u u return rat with
		ff =>	x		
		| tt =>	(mkpair nat nat (S Z) (S Z))		
	end.

Define mkrat := fun(x y : nat).(mkpair nat nat x y).


Define rplus := 
  fun (x y : rat). 
    (mkrat (plus (mult (numer x) (denom y))
                 (mult (numer y) (denom x)))
           (mult (denom x) (denom y))).

Define rmult := 
  fun (x y : rat). 
    (mkrat (mult (numer x) (numer y))
           (mult (denom x) (denom y))).

Define eqrat := fun(x y : rat).(eqnat (mult (numer x) (denom y)) (mult (numer y) (denom x))).
Define lt := fun(x y : rat).(lt (mult (numer x) (denom y)) (mult (numer y) (denom x))). 
Define le := fun (x y : rat).(or (lt x y) (eqrat x y)).

Define half := (mkrat (S Z) (S (S Z))).
Define quarter := (rmult half half).
Define zero := (mkrat Z (S Z)).
Define one := (mkrat (S Z) (S Z)).


Define numerTot : Forall(p:rat).Exists(z:nat).{ (numer p) = z } :=
	induction (p:rat) by x1 x2 IH return Exists(z:nat).{ (numer p) = z } with
		mkpair A' B' a' b' =>
			existsi cast a' by symm inj <pair * **> x2 { (numer p) = *}
			trans cong (numer *) x1
			join (numer (mkpair ! ! a' b')) a'			
	end.


Define denomTot : Forall(p:rat).Exists(z:nat).{ (denom p) = z } :=
	induction (p:rat) by x1 x2 IH return Exists(z:nat).{ (denom p) = z } with
		mkpair A' B' a' b' =>
			existsi cast b' by symm inj <pair ** *> x2 { (denom p) = *}
			trans cong (denom *) x1
			join (denom (mkpair ! ! a' b')) b'
	end.


Define rplus_zero : Forall(x:rat).{ (rplus x zero) = x } :=
	foralli(x:rat).
	abbrev p = (numer x) in
	abbrev q = (denom x) in	
	trans join (rplus x zero) 
                   (mkrat (plus (mult (numer x) (S Z)) (mult Z (denom x)))
                          (mult (denom x) (S Z)))
	trans cong (mkrat (plus * (mult Z (denom x))) (mult (denom x) (S Z)))
                [multOne p]
	trans cong (mkrat (plus (numer x) (mult Z (denom x))) *)
                [multOne q]
	trans cong (mkrat (plus (numer x) *) (denom x)) 
                join (mult Z (denom x)) Z
	trans cong (mkrat * (denom x)) [plusZ p]
	trans join (mkrat (numer x) (denom x)) 
		(mkpair nat nat (fst nat nat x) (snd nat nat x))
	[pair_lemma nat nat x].
	
	
Define rplus_comm : Forall(x y : rat).{ (rplus x y) = (rplus y x) } :=
	foralli(x y : rat).	
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	existse [numerTot y] foralli(ny:nat) (nyu:{ (numer y) = ny }).
	existse [denomTot y] foralli(dy:nat) (dyu:{ (denom y) = dy }).	
	existse [mult_total nx dy] foralli(z1:nat) (u1:{ (mult nx dy) = z1 }).
	existse [mult_total ny dx] foralli(z2:nat) (u2:{ (mult ny dx) = z2 }).
	trans join (rplus x y)
		(mkrat (plus (mult (numer x) (denom y)) (mult (numer y) (denom x))) (mult (denom x) (denom y)))
	trans cong (mkrat (plus (mult * (denom y)) (mult (numer y) (denom x))) (mult (denom x) (denom y))) nxu
	trans cong (mkrat (plus (mult nx (denom y)) (mult (numer y) *)) (mult * (denom y))) dxu
	trans cong (mkrat (plus (mult nx (denom y)) (mult * dx)) (mult dx (denom y))) nyu
	trans cong (mkrat (plus (mult nx *) (mult ny dx)) (mult dx *)) dyu
	trans cong (mkrat (plus * (mult ny dx)) (mult dx dy)) u1
	trans cong (mkrat (plus z1 *) (mult dx dy)) u2	
	trans cong (mkrat * (mult dx dy)) [plus_comm z1 z2]	
	trans cong (mkrat (plus z2 z1) *) [mult_comm dx dy]
	trans cong (mkrat (plus * z1) (mult dy dx)) symm u2	
	trans cong (mkrat (plus (mult ny dx) *) (mult dy dx)) symm u1
	trans cong (mkrat (plus (mult * dx) (mult nx dy)) (mult dy dx)) symm nyu
	trans cong (mkrat (plus (mult (numer y) *) (mult nx dy)) (mult dy *)) symm dxu
	trans cong (mkrat (plus (mult (numer y) (denom x)) (mult * dy)) (mult dy (denom x))) symm nxu
	trans cong (mkrat (plus (mult (numer y) (denom x)) (mult (numer x) *)) (mult * (denom x))) symm dyu
	join (mkrat (plus (mult (numer y) (denom x)) (mult (numer x) (denom y))) (mult (denom y) (denom x)))
	(rplus y x).


Define rmult_zero : Forall(x:rat).{ (eqrat (rmult x zero) zero) = tt } :=
	foralli (x:rat).
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	trans join (eqrat (rmult x zero) zero) 
		(eqrat (mkrat (mult (numer x) Z) (mult (denom x) (S Z))) zero)
	trans cong (eqrat (mkrat (mult * Z) (mult (denom x) (S Z))) zero) nxu
	trans cong (eqrat (mkrat (mult nx Z) (mult * (S Z))) zero) dxu	
	trans cong (eqrat (mkrat * (mult dx (S Z))) zero) [mult_comm Z nx]
	trans cong (eqrat (mkrat * (mult dx (S Z))) zero) [multZ nx]
	trans cong (eqrat (mkrat Z *) zero) [multOne dx]
	trans join (eqrat (mkrat Z dx) zero)
		(eqnat (mult Z (S Z)) (mult Z dx))
	trans cong (eqnat * (mult Z dx)) [multZ (S Z)]
	trans cong (eqnat Z *) join (mult Z dx) Z
	[eqnat_refl Z].
	
	
	
Define rmult_one : Forall(x:rat)(y:nat)(a:{y != Z}).{ (eqrat (rmult x (mkrat y y)) x) = tt } :=
	foralli(x:rat)(y:nat)(a:{y != Z}).
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	existse [mult_total dx y] foralli(mt1:nat) (mt1u:{ (mult dx y) = mt1 }).
	existse [mult_total nx mt1] foralli(mt2:nat) (mt2u:{ (mult nx mt1) = mt2 }).
		
	trans join (eqrat (rmult x (mkrat y y)) x)
		(eqrat (mkrat (mult (numer x) y) (mult (denom x) y)) x)
	trans join (eqrat (mkrat (mult (numer x) y) (mult (denom x) y)) x)
		(eqnat (mult (mult (numer x) y) (denom x)) (mult (numer x) (mult (denom x) y)))
	trans cong (eqnat (mult (mult * y) (denom x)) (mult * (mult (denom x) y))) nxu
	trans cong (eqnat (mult (mult nx y) *) (mult nx (mult * y))) dxu	
	trans cong (eqnat * (mult nx (mult dx y))) [mult_assoc nx y dx]
	trans cong (eqnat (mult nx *) (mult nx (mult dx y))) [mult_comm dx y]	
	trans cong (eqnat (mult nx *) (mult nx *)) mt1u
	trans cong (eqnat * *) mt2u
	[eqnat_refl mt2].
	
	
Define rmult_comm : Forall (x y : rat).{ (rmult x y) = (rmult y x) } :=
	foralli(x y : rat).
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	existse [numerTot y] foralli(ny:nat) (nyu:{ (numer y) = ny }).
	existse [denomTot y] foralli(dy:nat) (dyu:{ (denom y) = dy }).	
	trans join (rmult x y)
		(mkrat (mult (numer x) (numer y)) (mult (denom x) (denom y)))
	trans cong (mkrat (mult * (numer y)) (mult (denom x) (denom y))) nxu
	trans cong (mkrat (mult nx *) (mult (denom x) (denom y))) nyu
	trans cong (mkrat (mult nx ny) (mult * (denom y))) dxu
	trans cong (mkrat (mult nx ny) (mult dx *)) dyu
	trans cong (mkrat * (mult dx dy)) [mult_comm ny nx]
	trans cong (mkrat (mult ny nx) *) [mult_comm dy dx]
	trans cong (mkrat (mult * nx) (mult dy dx)) symm nyu
	trans cong (mkrat (mult (numer y) *) (mult dy dx)) symm nxu
	trans cong (mkrat (mult (numer y) (numer x)) (mult * dx)) symm dyu
	trans cong (mkrat (mult (numer y) (numer x)) (mult (denom y) *)) symm dxu
	join (mkrat (mult (numer y) (numer x)) (mult (denom y) (denom x))) (rmult y x).


Define rmult_assoc : Forall (x y z : rat).{ (rmult (rmult x y) z) = (rmult x (rmult y z)) } :=
	foralli (x y z : rat).
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	existse [numerTot y] foralli(ny:nat) (nyu:{ (numer y) = ny }).
	existse [denomTot y] foralli(dy:nat) (dyu:{ (denom y) = dy }).	
	existse [numerTot z] foralli(nz:nat) (nzu:{ (numer z) = nz }).
	existse [denomTot z] foralli(dz:nat) (dzu:{ (denom z) = dz }).
	trans join (rmult (rmult x y) z)
		(mkrat (mult (mult (numer x) (numer y)) (numer z)) (mult (mult (denom x) (denom y)) (denom z)))	
	trans cong (mkrat (mult (mult * (numer y)) (numer z)) (mult (mult (denom x) (denom y)) (denom z))) nxu
	trans cong (mkrat (mult (mult nx *) (numer z)) (mult (mult (denom x) (denom y)) (denom z))) nyu
	trans cong (mkrat (mult (mult nx ny) *) (mult (mult (denom x) (denom y)) (denom z))) nzu
	trans cong (mkrat (mult (mult nx ny) nz) (mult (mult * (denom y)) (denom z))) dxu
	trans cong (mkrat (mult (mult nx ny) nz) (mult (mult dx *) (denom z))) dyu
	trans cong (mkrat (mult (mult nx ny) nz) (mult (mult dx dy) *)) dzu
	trans cong (mkrat * (mult (mult dx dy) dz)) [mult_assoc nx ny nz]
	trans cong (mkrat (mult nx (mult ny nz)) *) [mult_assoc dx dy dz]
	trans cong (mkrat (mult * (mult ny nz)) (mult dx (mult dy dz))) symm nxu
	trans cong (mkrat (mult (numer x) (mult * nz)) (mult dx (mult dy dz))) symm nyu
	trans cong (mkrat (mult (numer x) (mult (numer y) *)) (mult dx (mult dy dz))) symm nzu
	trans cong (mkrat (mult (numer x) (mult (numer y) (numer z))) (mult * (mult dy dz))) symm dxu
	trans cong (mkrat (mult (numer x) (mult (numer y) (numer z))) (mult (denom x) (mult * dz))) symm dyu
	trans cong (mkrat (mult (numer x) (mult (numer y) (numer z))) (mult (denom x) (mult (denom y) *))) symm dzu
	join (mkrat (mult (numer x) (mult (numer y) (numer z))) (mult (denom x) (mult (denom y) (denom z)))) 
		(rmult x (rmult y z)).


Define rmult_switch : Forall (a b c d : rat).{ (rmult (rmult a b)(rmult c d)) = (rmult (rmult a c)(rmult b d)) } :=
	foralli(a b c d : rat).
	existse [numerTot a] foralli(na:nat) (nau:{ (numer a) = na }).
	existse [denomTot a] foralli(da:nat) (dau:{ (denom a) = da }).
	existse [numerTot b] foralli(nb:nat) (nbu:{ (numer b) = nb }).
	existse [denomTot b] foralli(db:nat) (dbu:{ (denom b) = db }).	
	existse [numerTot c] foralli(nc:nat) (ncu:{ (numer c) = nc }).
	existse [denomTot c] foralli(dc:nat) (dcu:{ (denom c) = dc }).
	existse [numerTot d] foralli(nd:nat) (ndu:{ (numer d) = nd }).
	existse [denomTot d] foralli(dd:nat) (ddu:{ (denom d) = dd }).	
	trans join (rmult (rmult a b)(rmult c d))
		(mkrat (mult (mult (numer a)(numer b))(mult (numer c)(numer d)))
			(mult (mult (denom a)(denom b))(mult (denom c)(denom d))))
	trans cong (mkrat (mult (mult * (numer b))(mult (numer c)(numer d))) (mult (mult (denom a)(denom b))(mult (denom c)(denom d)))) nau
	trans cong (mkrat (mult (mult na *)(mult (numer c)(numer d))) (mult (mult (denom a)(denom b))(mult (denom c)(denom d)))) nbu
	trans cong (mkrat (mult (mult na nb)(mult * (numer d))) (mult (mult (denom a)(denom b))(mult (denom c)(denom d)))) ncu
	trans cong (mkrat (mult (mult na nb)(mult nc *)) (mult (mult (denom a)(denom b))(mult (denom c)(denom d)))) ndu
	trans cong (mkrat (mult (mult na nb)(mult nc nd)) (mult (mult * (denom b))(mult (denom c)(denom d)))) dau
	trans cong (mkrat (mult (mult na nb)(mult nc nd)) (mult (mult da *)(mult (denom c)(denom d)))) dbu
	trans cong (mkrat (mult (mult na nb)(mult nc nd)) (mult (mult da db)(mult * (denom d)))) dcu
	trans cong (mkrat (mult (mult na nb)(mult nc nd)) (mult (mult da db)(mult dc *))) ddu
	trans cong (mkrat * (mult (mult da db)(mult dc dd))) [mult_switch na nb nc nd]	
	trans cong (mkrat (mult (mult na nc)(mult nb nd)) *) [mult_switch da db dc dd]	
	trans cong (mkrat (mult (mult * nc)(mult nb nd)) (mult (mult da dc)(mult db dd))) symm nau
	trans cong (mkrat (mult (mult (numer a) *)(mult nb nd)) (mult (mult da dc)(mult db dd))) symm ncu
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult * nd)) (mult (mult da dc)(mult db dd))) symm nbu
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult (numer b) *)) (mult (mult da dc)(mult db dd))) symm ndu
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult (numer b) (numer d))) 
			(mult (mult * dc)(mult db dd))) symm dau
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult (numer b) (numer d))) 
			(mult (mult (denom a) *)(mult db dd))) symm dcu
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult (numer b) (numer d))) 
			(mult (mult (denom a) (denom c)) (mult * dd))) symm dbu
	trans cong (mkrat (mult (mult (numer a) (numer c))(mult (numer b) (numer d))) 
			(mult (mult (denom a) (denom c)) (mult (denom b) *))) symm ddu
	join (mkrat (mult (mult (numer a) (numer c))(mult (numer b) (numer d))) 
			(mult (mult (denom a) (denom c)) (mult (denom b) (denom d))))
		(rmult (rmult a c)(rmult b d)).	
	

Define rmult_cong1 : Forall(r1 r2 x:rat)(u:{(eqrat r1 r2) = tt}).{(eqrat (rmult r1 x) (rmult r2 x)) = tt} :=
	foralli(r1 r2 x:rat)(u:{(eqrat r1 r2) = tt}).
	existse [numerTot r1] foralli(nr1:nat) (nr1u:{ (numer r1) = nr1 }).
	existse [denomTot r1] foralli(dr1:nat) (dr1u:{ (denom r1) = dr1 }).
	existse [numerTot r2] foralli(nr2:nat) (nr2u:{ (numer r2) = nr2 }).
	existse [denomTot r2] foralli(dr2:nat) (dr2u:{ (denom r2) = dr2 }).	
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	trans join (eqrat (rmult r1 x) (rmult r2 x))
		(eqnat (mult (mult (numer r1)(numer x)) (mult (denom r2)(denom x)))
			(mult (mult (numer r2) (numer x)) (mult (denom r1)(denom x))))
	trans cong (eqnat (mult (mult * (numer x)) (mult (denom r2)(denom x)))
			(mult (mult (numer r2) (numer x)) (mult (denom r1)(denom x)))) nr1u
	trans cong (eqnat (mult (mult nr1 *) (mult (denom r2)(denom x)))
			(mult (mult (numer r2) *) (mult (denom r1)(denom x)))) nxu
	trans cong (eqnat (mult (mult nr1 nx) (mult * (denom x))) 
			(mult (mult (numer r2) nx) (mult (denom r1)(denom x)))) dr2u
	trans cong (eqnat (mult (mult nr1 nx) (mult dr2 *)) (mult (mult (numer r2) nx) (mult (denom r1) *))) dxu
	trans cong (eqnat (mult (mult nr1 nx) (mult dr2 dx)) (mult (mult * nx) (mult (denom r1) dx))) nr2u
	trans cong (eqnat (mult (mult nr1 nx) (mult dr2 dx)) (mult (mult nr2 nx) (mult * dx))) dr1u	
	trans cong (eqnat * (mult (mult nr2 nx) (mult dr1 dx))) [mult_switch nr1 nx dr2 dx]	
	trans cong (eqnat (mult (mult nr1 dr2) (mult nx dx)) *) [mult_switch nr2 nx dr1 dx]
	existse [mult_total nr1 dr2] foralli(mt1:nat) (mt1u:{ (mult nr1 dr2) = mt1 }).
	existse [mult_total nr2 dr1] foralli(mt2:nat) (mt2u:{ (mult nr2 dr1) = mt2 }).	
	trans cong (eqnat (mult * (mult nx dx)) (mult (mult nr2 dr1) (mult nx dx))) mt1u	
	trans cong (eqnat (mult * (mult nx dx)) (mult (mult nr2 dr1) (mult nx dx)))
		[eqnatEq mt1 mt2			
			trans cong (eqnat * mt2) symm mt1u
			trans cong (eqnat (mult nr1 dr2) *) symm mt2u
			trans cong (eqnat (mult nr1 dr2) (mult nr2 *)) symm dr1u
			trans cong (eqnat (mult nr1 dr2) (mult * (denom r1))) symm nr2u
			trans cong (eqnat (mult nr1 *) (mult (numer r2)(denom r1))) symm dr2u
			trans cong (eqnat (mult * (denom r2)) (mult (numer r2)(denom r1))) symm nr1u			
			trans join (eqnat (mult (numer r1)(denom r2)) (mult (numer r2)(denom r1))) 
				(eqrat r1 r2) 
			u ]	
	existse [mult_total nx dx] foralli(mt3:nat) (mt3u:{ (mult nx dx) = mt3 }).
	existse [mult_total mt2 mt3] foralli(mt4:nat) (mt4u:{ (mult mt2 mt3) = mt4 }).	
	trans cong (eqnat (mult mt2 (mult nx dx)) (mult * (mult nx dx))) mt2u
	trans cong (eqnat (mult mt2 *) (mult mt2 *)) mt3u
	trans cong (eqnat * *) mt4u
	[eqnat_refl mt4].


Define rplus_assoc : Forall(x y z : rat).{ (eqrat (rplus (rplus x y) z) (rplus x (rplus y z))) = tt } :=
	foralli(x y z: rat).
	existse [numerTot x] foralli(nx:nat) (nxu:{ (numer x) = nx }).
	existse [denomTot x] foralli(dx:nat) (dxu:{ (denom x) = dx }).
	existse [numerTot y] foralli(ny:nat) (nyu:{ (numer y) = ny }).
	existse [denomTot y] foralli(dy:nat) (dyu:{ (denom y) = dy }).	
	existse [numerTot z] foralli(nz:nat) (nzu:{ (numer z) = nz }).
	existse [denomTot z] foralli(dz:nat) (dzu:{ (denom z) = dz }).	
	trans join (eqrat (rplus (rplus x y) z) (rplus x (rplus y z)))
		(eqrat (mkrat (plus (mult (plus (mult (numer x) (denom y)) (mult (numer y) (denom x))) (denom z)) 
					(mult (numer z) (mult (denom x) (denom y)))) (mult (mult (denom x) (denom y)) (denom z)))
			(mkrat (plus (mult (numer x) (mult (denom y) (denom z))) 
					(mult (plus (mult (numer y) (denom z)) (mult (numer z) (denom y))) (denom x))) 
				(mult (denom x) (mult (denom y) (denom z)))) )

	trans cong (eqrat (mkrat (plus (mult (plus (mult * (denom y)) (mult (numer y) (denom x))) (denom z)) 
					(mult (numer z) (mult (denom x) (denom y)))) (mult (mult (denom x) (denom y)) (denom z)))
			(mkrat (plus (mult * (mult (denom y) (denom z))) 
					(mult (plus (mult (numer y) (denom z)) (mult (numer z) (denom y))) (denom x))) 
				(mult (denom x) (mult (denom y) (denom z)))) ) nxu

	trans cong (eqrat (mkrat (plus (mult (plus (mult nx *) (mult (numer y) (denom x))) (denom z)) 
					(mult (numer z) (mult (denom x) *))) (mult (mult (denom x) *) (denom z)))
			(mkrat (plus (mult nx (mult * (denom z))) 
					(mult (plus (mult (numer y) (denom z)) (mult (numer z) *)) (denom x))) 
				(mult (denom x) (mult * (denom z)))) ) dyu

	trans cong (eqrat (mkrat (plus (mult (plus (mult nx dy) (mult * (denom x))) (denom z)) 
					(mult (numer z) (mult (denom x) dy))) (mult (mult (denom x) dy) (denom z)))
			(mkrat (plus (mult nx (mult dy (denom z))) 
					(mult (plus (mult * (denom z)) (mult (numer z) dy)) (denom x))) 
				(mult (denom x) (mult dy (denom z)))) ) nyu

	trans cong (eqrat (mkrat (plus (mult (plus (mult nx dy) (mult ny *)) (denom z)) 
					(mult (numer z) (mult * dy))) (mult (mult * dy) (denom z)))
			(mkrat (plus (mult nx (mult dy (denom z))) (mult (plus (mult ny (denom z)) (mult (numer z) dy)) *)) 
				(mult * (mult dy (denom z)))) ) dxu

	trans cong (eqrat (mkrat (plus (mult (plus (mult nx dy) (mult ny dx)) *) 
					(mult (numer z) (mult dx dy))) (mult (mult dx dy) *))
			(mkrat (plus (mult nx (mult dy *)) (mult (plus (mult ny *) (mult (numer z) dy)) dx)) 
				(mult dx (mult dy *))) ) dzu

	trans cong (eqrat (mkrat (plus (mult (plus (mult nx dy) (mult ny dx)) dz) 
					(mult * (mult dx dy))) (mult (mult dx dy) dz))
			(mkrat (plus (mult nx (mult dy dz)) (mult (plus (mult ny dz) (mult * dy)) dx)) 
					(mult dx (mult dy dz))) ) nzu

	trans join (eqrat 
			(mkrat (plus (mult (plus (mult nx dy) (mult ny dx)) dz) (mult nz (mult dx dy))) (mult (mult dx dy) dz))
			(mkrat (plus (mult nx (mult dy dz)) (mult (plus (mult ny dz) (mult nz dy)) dx)) (mult dx (mult dy dz))) )
		(eqnat 
			(mult (plus (mult (plus (mult nx dy) (mult ny dx)) dz) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
			(mult (plus (mult nx (mult dy dz)) (mult (plus (mult ny dz) (mult nz dy)) dx)) (mult (mult dx dy) dz)) )
		
	existse [mult_total nx dy] foralli(mt1:nat) (mt1u:{ (mult nx dy) = mt1 }).
	existse [mult_total ny dx] foralli(mt2:nat) (mt2u:{ (mult ny dx) = mt2 }).	
	existse [mult_total ny dz] foralli(mt3:nat) (mt3u:{ (mult ny dz) = mt3 }).	
	existse [mult_total nz dy] foralli(mt4:nat) (mt4u:{ (mult nz dy) = mt4 }).	
	
	trans cong (eqnat (mult (plus (mult (plus * (mult ny dx)) dz) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (mult (plus (mult ny dz) (mult nz dy)) dx)) (mult (mult dx dy) dz)) ) mt1u
		
	trans cong (eqnat (mult (plus (mult (plus mt1 *) dz) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (mult (plus (mult ny dz) (mult nz dy)) dx)) (mult (mult dx dy) dz)) ) mt2u
	
	trans cong (eqnat (mult (plus (mult (plus mt1 mt2) dz) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (mult (plus * (mult nz dy)) dx)) (mult (mult dx dy) dz)) ) mt3u
			
	trans cong (eqnat (mult (plus (mult (plus mt1 mt2) dz) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (mult (plus mt3 *) dx)) (mult (mult dx dy) dz)) ) mt4u
	
	trans cong (eqnat (mult (plus * (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (mult (plus mt3 mt4) dx)) (mult (mult dx dy) dz)) ) [mult_dist_2 dz mt1 mt2]
		
	trans cong (eqnat (mult (plus (plus (mult mt1 dz) (mult mt2 dz)) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) *) (mult (mult dx dy) dz)) ) [mult_dist_2 dx mt3 mt4 ]
	
	trans cong (eqnat (mult (plus (plus (mult * dz) (mult mt2 dz)) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (plus (mult mt3 dx) (mult mt4 dx))) (mult (mult dx dy) dz))) symm mt1u

	trans cong (eqnat 
		(mult (plus (plus (mult (mult nx dy) dz) (mult * dz)) (mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (plus (mult mt3 dx) (mult mt4 dx))) (mult (mult dx dy) dz))) symm mt2u

	trans cong (eqnat 
		(mult (plus (plus (mult (mult nx dy) dz)(mult (mult ny dx) dz))(mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz)) (plus (mult * dx) (mult mt4 dx))) (mult (mult dx dy) dz))) symm mt3u
	
	trans cong (eqnat 
		(mult (plus (plus (mult (mult nx dy) dz)(mult (mult ny dx) dz))(mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult * dx)))(mult (mult dx dy) dz))) symm mt4u
	
	trans cong (eqnat 
		(mult (plus (plus * (mult (mult ny dx) dz))(mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) 
		[mult_assoc nx dy dz]

	trans cong (eqnat 
		(mult (plus (plus (mult nx (mult dy dz)) * )(mult nz (mult dx dy))) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) 
		[mult_switch2 ny dx dz]

	trans cong (eqnat 
		(mult (plus (plus (mult nx (mult dy dz))(mult (mult ny dz) dx))(mult nz *)) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) 
		[mult_comm dy dx]

	trans cong (eqnat 
		(mult (plus (plus (mult nx (mult dy dz))(mult (mult ny dz) dx)) *) (mult dx (mult dy dz))) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) 
		symm [mult_assoc nz dy dx]

	trans cong (eqnat 
		(mult (plus (plus (mult nx (mult dy dz))(mult (mult ny dz) dx))(mult (mult nz dy) dx)) *) 
		(mult (plus (mult nx (mult dy dz))(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) 
		symm [mult_assoc dx dy dz]

	existse [mult_total dy dz] foralli(mt5:nat) (mt5u:{ (mult dy dz) = mt5 }).
	existse [mult_total ny dz] foralli(mt6:nat) (mt6u:{ (mult ny dz) = mt6 }).
	existse [mult_total nz dy] foralli(mt7:nat) (mt7u:{ (mult nz dy) = mt7 }).
	existse [mult_total nx mt5] foralli(mt8:nat) (mt8u:{ (mult nx mt5) = mt8 }).
	existse [mult_total mt6 dx] foralli(mt9:nat) (mt9u:{ (mult mt6 dx) = mt9 }).
	existse [mult_total mt7 dx] foralli(mtx:nat) (mtxu:{ (mult mt7 dx) = mtx }).

	trans cong (eqnat 
		(mult (plus (plus (mult nx *)(mult (mult ny dz) dx))(mult (mult nz dy) dx))(mult (mult dx dy) dz)) 
		(mult (plus (mult nx *)(plus (mult (mult ny dz) dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) mt5u
		
	trans cong (eqnat (mult (plus (plus (mult nx mt5)(mult * dx))(mult (mult nz dy) dx))(mult (mult dx dy) dz)) 
		(mult (plus (mult nx mt5)(plus (mult * dx)(mult (mult nz dy) dx)))(mult (mult dx dy) dz))) mt6u

	trans cong (eqnat (mult (plus (plus (mult nx mt5)(mult mt6 dx))(mult * dx))(mult (mult dx dy) dz)) 
		(mult (plus (mult nx mt5)(plus (mult mt6 dx)(mult * dx)))(mult (mult dx dy) dz))) mt7u

	trans cong (eqnat (mult (plus (plus * (mult mt6 dx))(mult mt7 dx))(mult (mult dx dy) dz)) 
		(mult (plus * (plus (mult mt6 dx)(mult mt7 dx)))(mult (mult dx dy) dz))) mt8u

	trans cong (eqnat (mult (plus (plus mt8 *)(mult mt7 dx))(mult (mult dx dy) dz)) 
		(mult (plus mt8 (plus * (mult mt7 dx)))(mult (mult dx dy) dz))) mt9u

	trans cong (eqnat (mult (plus (plus mt8 mt9) *)(mult (mult dx dy) dz)) 
		(mult (plus mt8 (plus mt9 *))(mult (mult dx dy) dz))) mtxu

	trans cong (eqnat (mult * (mult (mult dx dy) dz)) 
		(mult (plus mt8 (plus mt9 mtx))(mult (mult dx dy) dz))) [plus_assoc mt8 mt9 mtx]

	existse [plus_total mtx mt9] foralli(pta:nat) (ptau:{ (plus mt9 mtx) = pta }).
	existse [plus_total pta mt8] foralli(ptb:nat) (ptbu:{ (plus mt8 pta) = ptb }).
	existse [mult_total dx dy] foralli(mta:nat) (mtau:{ (mult dx dy) = mta }).
	existse [mult_total mta dz] foralli(mtb:nat) (mtbu:{ (mult mta dz) = mtb }).
	existse [mult_total ptb mtb] foralli(mtz:nat) (mtzu:{ (mult ptb mtb) = mtz }).

	trans cong (eqnat (mult (plus mt8 *) (mult (mult dx dy) dz)) (mult (plus mt8 *) (mult (mult dx dy) dz)) ) ptau
	trans cong (eqnat (mult (plus mt8 pta)(mult * dz)) (mult (plus mt8 pta)(mult * dz))) mtau
	trans cong (eqnat (mult * (mult mta dz)) (mult * (mult mta dz))) ptbu
	trans cong (eqnat (mult ptb *) (mult ptb *)) mtbu
	trans cong (eqnat * *) mtzu		
	[eqnat_refl mtz].



