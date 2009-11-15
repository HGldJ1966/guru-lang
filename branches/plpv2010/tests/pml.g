Include "../lib/nat.g".
Include "../lib/mult.g".
Include "../lib/pair.g".
Include "../lib/list.g".
Include "../lib/msort.g".

Define natp : type := <pair nat nat>.
Define ml : type := <list natp>.
Define pml : type := <list ml>.

Inductive pme : type :=
	  nate  : Fun(p:<pair nat nat>).pme
	| pluse : Fun(x y : pme).pme
	| multe : Fun(x y : pme).pme.

%- perform an interpretive evaluation of a pme -%
Define interp : Fun (x:pme).nat :=
	fun interp(x:pme) : nat.
	match x return nat with
		  nate n => 		(fst nat nat n)
		| pluse e1 e2 => 	(plus (interp e1)(interp e2))
		| multe e1 e2 =>	(mult (interp e1)(interp e2))
	end.

%- perform an interpretive evaluation of a multlist -%
Define interp_ml : Fun (x:ml).nat :=
	fun interp_ml (x:ml) : nat.
	match x by u v return nat with
		nil A' => (S Z)
		| cons A' a' l' =>
			abbrev p = symm inj <list *> v in
			(mult (fst nat nat cast a' by p) (interp_ml cast l' by cong <list *> p))
	end.

%- perform an interpretive evaluation of a plusmultlist -%
Define interp_pml : Fun (x:pml).nat :=
	fun interp_pml (x:pml) : nat.
	match x by u v return nat with
		nil A' => Z
		| cons A' a' l' =>
			abbrev p = symm inj <list *> v in
			(plus (interp_ml cast a' by p) (interp_pml cast l' by cong <list *> p))
	end.

Define interp_mlf_f := fun(owned x:natp)(y:nat).(mult (fst nat nat x) y).

Define interp_mlf : Fun(x:ml).nat :=
  fun(x:ml).
  (foldr natp nat interp_mlf_f (S Z) x).

Define interp_pmlf_f := fun(owned x:ml)(y:nat).(plus (interp_mlf x) y).

Define interp_pmlf : Fun(x:pml).nat :=
  fun(x:pml).
  (foldr ml nat interp_pmlf_f Z x).

%- compare (the ordering of) two pm vars; tt iff x less than or equal to y -%
Define cmp_natp : Fun(x y : natp).bool := fun(x y : natp).(le (snd nat nat x)(snd nat nat y)).

%- compare (lexicographically) the constituent pmvars of two multlists; -%
%- tt iff x less than or equal to y -%
Define cmp_ml : Fun(x y : ml).bool :=
	fun cmp_ml(x y : ml) : bool.
	match x by ux vx return bool with
		  nil Ax' => tt
		| cons Ax' ax' lx' =>
			match y by uy vy return bool with
				  nil Ay' => ff
				| cons Ay' ay' ly' =>
					abbrev p = symm inj <list *> vx in
					abbrev q = symm inj <list *> vy in
					match (eqnat (snd nat nat cast ax' by p) (snd nat nat cast ay' by q)) by x y return bool with
						  ff => (lt (snd nat nat cast ax' by p)(snd nat nat cast ay' by q))
						| tt => (cmp_ml cast lx' by cong <list *> p cast ly' by cong <list *> q)
					end
			end
	end.

%- multiply a term with another term; does not maintain ordering -%
Define multTT : Fun (x y : ml).ml := fun(x y : ml).(append natp x y).

%- multiply a formula with another term -%
Define multFT : Fun (x:pml)(y:ml).pml :=
	fun multFT(x:pml)(y:ml) : pml.
	match x by u v return pml with
		  nil A' => x
		| cons A' a' l' =>
			abbrev p = symm inj <list *> v in
			(cons ml (multTT cast a' by p y) (multFT cast l' by cong <list *> p y))
	end.

%- add two formulas; does not maintain term ordering -%
Define plusFF : Fun (x y : pml).pml := fun(x y : pml).(append ml x y).
%-
Define plusFF :=
  fun plusFF(x y : pml):pml.
    match x by x1 x2 return pml with
      nil ml' => y
    | cons ml' h t => match y by y1 y2 return pml with
                          nil ml'' => x
                        | cons ml'' h' t' => (cons ml cast h by symm inj <list *> x2 (cons ml cast h' by symm inj <list *> y2 (plusFF cast t by symm x2 cast t' by symm y2)))
                        end
    end.
-%

%- multiply two formulas -%
Define multFF : Fun(x y : pml).pml :=
	fun multFF(x y : pml) : pml.
	match x by ux vx return pml with
		  nil Ax' => (nil ml)
		| cons Ax' ax' lx' =>
			match y by uy vy return pml with
				  nil Ay' => (nil ml)
				| cons Ay' ay' ly' =>
					abbrev p = symm inj <list *> vy in
					(plusFF (multFT x cast ay' by p) (multFF x cast ly' by cong <list *> p))
			end
	end.

%- convert a pmexpr to a plusmultlist -%
Define flatten : Fun (x:pme).pml :=
	fun flatten (x:pme) : pml.
	match x return pml with
		  nate n =>		(cons ml (cons natp n (nil natp)) (nil ml))
		| pluse e1 e2 =>	(plusFF (flatten e1) (flatten e2))
		| multe e1 e2 =>	(multFF (flatten e1) (flatten e2))
	end.

%- sort all constituent multlists of a plusmultlist (without sorting the top-level plusmultlist) -%
Define sort_pml_helper : Fun(x:pml).pml :=
	fun sort_pml_helper (x:pml) : pml.
	match x by u v return pml with
		  nil A' => x
		| cons A' a' l' =>
			abbrev p = symm inj <list *> v in
			(cons ml (msort natp cast a' by p cmp_natp) (sort_pml_helper cast l' by cong <list *> p))
	end.

%- sort a plusmultlist according to pmvar ordering (snd pmvar) and pmterm ordering (lexicographical) -%
Define sort_pml : Fun (x:pml).pml :=
	fun sort_pml (x:pml) : pml.
	match x return pml with
		  nil A' => x
		| cons A' a' l' =>
			(msort ml (sort_pml_helper x) cmp_ml)
	end.

%- canonicalize a pme -%
Define simplify : Fun (x:pme).pml := fun(x:pme).(sort_pml (flatten x)).

%-
Set "print_parsed".

Define result1	:= (flatten (multe (nate (mkpair nat nat one one))(nate (mkpair nat nat two two)))).
Interpret result1.
Define result2	:= (flatten (pluse (nate (mkpair nat nat one one))(nate (mkpair nat nat two two)))).
Interpret result2.
Define result3 := (flatten (multe (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))))).
Define result3a := (flatten (multe (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))) (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) )).

Define result1	:= (simplify (multe (nate (mkpair nat nat one one))(nate (mkpair nat nat two two)))).
Interpret result1. %- (1 * 2) -%
Define result2	:= (simplify (pluse (nate (mkpair nat nat one one))(nate (mkpair nat nat two two)))).
Interpret result2. %- (1 + 2) -%
Define result3 := (simplify (multe (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))))).
Interpret result3. %- ((1 + 2) * (3 + 4)) -%
Define result3a := (simplify (multe (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))) (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) )).
Interpret result3a. %- ((3 + 4) * (1 + 2)) -%
Define result3b := (interp (multe (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))) (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) )).
Interpret result3b.
Define result3c := (interp_pml (flatten (multe (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))) (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) ))).
Interpret result3c.
Define result3d := (interp_pml (simplify (multe (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))) (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) ))).
Interpret result3d.
Define result3e := (interp_pml result3a).
Interpret result3e.

Define ml1 := (cons natp (mkpair nat nat one one) (cons natp (mkpair nat nat three three) (cons natp (mkpair nat nat two two) (nil natp)))).
Define result4 := (msort natp ml1 cmp_natp).
Interpret result4.
Define result4a := (le (snd nat nat (hd natp (tl natp ml1))) (snd nat nat (hd natp ml1))).
Interpret result4a.
Define result5 := (sort_pml result3).
Interpret result5.
Define result5a := (sort_pml result3a).
Interpret result5a.

Define result6 := (interp (multe (pluse (nate (mkpair nat nat one one)) (nate (mkpair nat nat two two))) (pluse (nate (mkpair nat nat three three)) (nate (mkpair nat nat four four))))).
Interpret result6.
Define result6a := (interp_pml result5a).
Interpret result6a.


-%

