Include "nat.g".

Define P : Fun(n:nat).nat :=
	fun(n : nat).
	match n by x y return nat with
		Z => abort nat
		| S n' => n'
	end.
	
	
Define PS_lemma : Forall(n:nat).{ (P (S n)) = n } :=
	induction (n:nat) by x1 x2 IH return { (P (S n)) = n } with
	Z => trans cong (P (S *)) x1
		trans join (P (S Z)) Z
		symm x1
	| S n' => trans cong (P (S *)) x1
		trans join (P (S (S n'))) (S n')
		symm x1
	end.

Define PS_lemma2 : Forall(n:nat)(a:{n != Z}).{ (S (P n)) = n } :=
	induction(n:nat) by x1 x2 IH return Forall(a:{n != Z}).{ (S (P n)) = n } with
	Z => foralli(a:{n != Z}).
		contra trans symm x1 a
			{ (S (P n)) = n }
	| S n' => foralli(a:{n != Z}).
			trans cong (S (P *)) x1
			trans join (S (P (S n'))) (S n')
			symm x1
	end.			

Define P_total : Forall(n:nat)(u:{n != Z}).Exists(z:nat).{(P n) = z} :=
	induction(n:nat) by x1 x2 IH return Forall(u:{n != Z}).Exists(z:nat).{(P n) = z} with
	Z => foralli(u:{n != Z}).
		contra trans symm x1 u
			Exists(z:nat).{(P n) = z}
	| S n' => foralli(u:{n != Z}).
		 existsi n' {(P n) = *}
		 	trans cong (P *) x1
			join (P (S n')) n'
	end.

Define S_to_P: Forall(a b:nat)(u:{(S a) = b}).{a = (P b)} :=
	foralli(a b:nat)(u:{(S a) = b}). symm trans cong (P *) symm u [PS_lemma a].