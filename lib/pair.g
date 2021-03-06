%Set "print_parsed".


Inductive pair : Fun(A B:type).type :=
  mkpair : Fun(A B:type)(a:A)(b:B).<pair A B>.

Define decomp_pair : Forall(A B:type)(x:<pair A B>).
                     Exists(a:A)(b:B).{x = (mkpair ! ! a b)} :=
  foralli(A B:type).
     induction(x:<pair A B>) by x1 x2 IH 
       return Exists(a:A)(b:B).{x = (mkpair ! ! a b)}
     with
       mkpair A' B' a b => 
          existsi cast a by symm inj <pair * **> x2
            Exists(b:B).{x = (mkpair ! ! * b)}
            existsi cast b by symm inj <pair ** *> x2
              {x = (mkpair ! ! a *)} 
              x1
       end.


Define fst : Fun(A B :type)(owned p:<pair A B>).A :=
	fun fst(A B :type)(owned p:<pair A B>) : A.
	match p by x1 x2 return A with
		mkpair A' B' a' b' => inc cast a' by symm inj <pair * **> x2
	end.	


Define snd : Fun(A B :type)(owned p:<pair A B>).B :=
	fun snd(A B :type)(owned p:<pair A B>) : B.
	match p by x1 x2 return B with
		mkpair A' B' a' b' => inc cast b' by symm inj <pair ** *> x2
	end.	


Define pair_total : Forall(A B : type)(a : A)(b: B).Exists(p:<pair A B>).{ (mkpair ! ! a b) = p} :=
       foralli(A B : type)(a : A)(b: B). 
       		existsi (mkpair A B a b) {(mkpair ! ! a b) = *}
       		join (mkpair A B a b) (mkpair A B a b).		


Define fstTot : Forall(A B : type)(p:<pair A B>).Exists(z:A).{ (fst ! ! p) = z } :=
	foralli(A B : type).
	induction (p:<pair A B>) by x1 x2 IH return Exists(z:A).{ (fst ! ! p) = z } with
		mkpair A' B' a' b' =>
			existsi cast a' by symm inj <pair * **> x2 { (fst ! ! p) = *}
			trans cong (fst ! ! *) x1
			join (fst ! ! (mkpair ! ! a' b')) a'
	end.

	
Define sndTot : Forall(A B : type)(p:<pair A B>).Exists(z:B).{ (snd ! ! p) = z } :=
	foralli(A B : type).
	induction (p:<pair A B>) by x1 x2 IH return Exists(z:B).{ (snd ! ! p) = z } with
		mkpair A' B' a' b' =>
			existsi cast b' by symm inj <pair ** *> x2 { (snd ! ! p) = *}
			trans cong (snd ! ! *) x1
			join (snd ! ! (mkpair ! ! a' b')) b'
	end.


Define pair_lemma : Forall(A B : type)(p:<pair A B>).{ (mkpair ! ! (fst ! ! p) (snd ! ! p)) = p } :=
	foralli(A B : type).
	induction (p:<pair A B>) by x1 x2 IH return { (mkpair ! ! (fst ! ! p) (snd ! ! p)) = p } with
		mkpair A' B' a' b' =>
			trans cong (mkpair ! ! (fst ! ! *) (snd ! ! *)) x1
			trans join (mkpair ! ! (fst ! ! (mkpair ! ! a' b')) (snd ! ! (mkpair ! ! a' b')))
				(mkpair ! ! a' b')
			symm x1
	end.

	
	
	
	
