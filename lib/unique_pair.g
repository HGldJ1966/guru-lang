%Set "print_parsed".

Include "unique.g".
Include "unique_owned.g".
Include "bool.g".

Inductive unique_pair : Fun(A B:type).type :=
  mk_unique_pair : Fun(A B:type)(a:A)(#unique b:B).#unique <unique_pair A B>.

Define unique_decomp_pair : Forall(A B : type)(x : <unique_pair A B>).
                     Exists(a:A)(b:B).{x = (mk_unique_pair ! ! a b)} :=
  foralli(A B:type).
     induction(x: <unique_pair A B>) by x1 x2 IH 
       return Exists(a:A)(b:B).{x = (mk_unique_pair ! ! a b)}
     with
       mk_unique_pair A' B' a b => 
          existsi cast a by symm inj <unique_pair * **> x2
            Exists(b:B).{x = (mk_unique_pair ! ! * b)}
            existsi cast b by symm inj <unique_pair ** *> x2
              {x = (mk_unique_pair ! ! a *)} 
              x1
       end.


Define unique_fst : Fun(A B :type)(^#unique_owned p:<unique_pair A B>).A :=
	fun unique_fst(A B :type)(^#unique_owned p:<unique_pair A B>) : A.
	match p by x1 x2 return A with
		mk_unique_pair _ _ a' b' => (inc A a')
	end.	


Define unique_snd : Fun(A B :type)(^#unique_owned p:<unique_pair A B>).B :=
	fun snd(A B :type)(^#unique_owned p:<unique_pair A B>) : B.
	match p by x1 x2 return B with
		mk_unique_pair _ _ a' b' => (inc B b')
	end.	

Define unique_pair_total : Forall(A B : type)(a : A)(b: B).Exists(p:<unique_pair A B>).{ (mk_unique_pair ! ! a b) = p} :=
       foralli(A B : type)(a : A)(b: B). 
       		existsi (mk_unique_pair A B a b) {(mk_unique_pair ! ! a b) = *}
       		join (mk_unique_pair A B a b) (mk_unique_pair A B a b).		


Define unique_fstTot : Forall(A B : type)(p:<unique_pair A B>).Exists(z:A).{ (unique_fst ! ! p) = z } :=
	foralli(A B : type).
	induction (p:<unique_pair A B>) by x1 x2 IH return Exists(z:A).{ (unique_fst ! ! p) = z } with
		mk_unique_pair A' B' a' b' =>
			existsi cast a' by symm inj <unique_pair * **> x2 { (unique_fst ! ! p) = *}
			trans cong (unique_fst ! ! *) x1
			join (unique_fst ! ! (mk_unique_pair ! ! a' b')) a'
	end.

	
Define unique_sndTot : Forall(A B : type)(p:<unique_pair A B>).Exists(z:B).{ (unique_snd ! ! p) = z } :=
	foralli(A B : type).
	induction (p:<unique_pair A B>) by x1 x2 IH return Exists(z:B).{ (unique_snd ! ! p) = z } with
		mk_unique_pair A' B' a' b' =>
			existsi cast b' by symm inj <unique_pair ** *> x2 { (unique_snd ! ! p) = *}
			trans cong (unique_snd ! ! *) x1
			join (unique_snd ! ! (mk_unique_pair ! ! a' b')) b'
	end.


Define unique_pair_lemma : Forall(A B : type)(p:<unique_pair A B>).{ (mk_unique_pair ! ! (unique_fst ! ! p) (unique_snd ! ! p)) = p } :=
	foralli(A B : type).
	induction (p:<unique_pair A B>) by x1 x2 IH return { (mk_unique_pair ! ! (unique_fst ! ! p) (unique_snd ! ! p)) = p } with
		mk_unique_pair A' B' a' b' =>
			trans cong (mk_unique_pair ! ! (unique_fst ! ! *) (unique_snd ! ! *)) x1
			trans join (mk_unique_pair ! ! (unique_fst ! ! (mk_unique_pair ! ! a' b')) (unique_snd ! ! (mk_unique_pair ! ! a' b')))
				(mk_unique_pair ! ! a' b')
			symm x1
	end.

	
Define eq_unique_pair : Fun(A B:type)(eqA:Fun(x y : A). bool)(eqB:Fun(x y : B). bool)(^#unique_owned p1 p2 : <unique_pair A B>). bool :=
  fun(A B:type)(eqA:Fun(x y : A). bool)(eqB:Fun(x y : B). bool)(^#unique_owned p1 p2 : <unique_pair A B>).
    (and (eqA (unique_fst A B p1) (unique_fst A B p2)) (eqB (unique_snd A B p1) (unique_snd A B p2))).
