Include "pml.g".

%- interp is total -%
Define interpTot : Forall(x:pme).Exists(z:nat).{ (interp x) = z } :=
	induction (x:pme) by x1 x2 IHx return Exists(z:nat).{ (interp x) = z } with
		  nate n =>
			existsi terminates (fst nat nat n) by fstTot
                                { (interp x) = * }
			  trans cong (interp *) x1
			  join (interp (nate n)) (fst nat nat n)
		| pluse e1 e2 =>
			existsi terminates (plus terminates (interp e1) by [IHx e1]
                                                 terminates (interp e2) by [IHx e2]) by plus_total
                                { (interp x) = * }
			  trans cong (interp *) x1
			  join (interp (pluse e1 e2)) (plus (interp e1) (interp e2))
		| multe e1 e2 =>
			existsi terminates (mult terminates (interp e1) by [IHx e1]
                                                 terminates (interp e2) by [IHx e2]) by mult_total
                                { (interp x) = * }
			  trans cong (interp *) x1
			  join (interp (multe e1 e2)) (mult (interp e1) (interp e2))
	end.

%- interp_ml is total -%
Define interp_mlTot : Forall(x:ml).Exists(z:nat).{ (interp_ml x) = z } :=
	induction (x:ml) by x1 x2 IHx return Exists(z:nat).{ (interp_ml x) = z } with
		  nil A' =>
			existsi (S Z) { (interp_ml x) = * }
			  trans cong (interp_ml *) x1
			  join (interp_ml (nil A')) (S Z)
		| cons A' a' l' =>
			abbrev p = symm inj <list *> x2 in
			existsi terminates (mult terminates (fst nat nat cast a' by p) by fstTot
                                                 terminates (interp_ml cast l' by cong <list *> p) by [IHx cast l' by cong <list *> p]) by mult_total
				{ (interp_ml x) = * }
			  trans cong (interp_ml *) x1
			  join (interp_ml (cons A' a' l'))
			       (mult (fst nat nat cast a' by p) (interp_ml cast l' by cong <list *> p))
	end.

%- interp_pml is total -%
Define interp_pmlTot : Forall(x:pml).Exists(z:nat).{ (interp_pml x) = z } :=
	induction (x:pml) by x1 x2 IHx return Exists(z:nat).{ (interp_pml x) = z } with
		  nil A' =>
			existsi Z { (interp_pml x) = * }
			  trans cong (interp_pml *) x1
			  join (interp_pml (nil A')) Z
		| cons A' a' l' =>
			abbrev p = symm inj <list *> x2 in
			existsi terminates (plus terminates (interp_ml cast a' by p) by [interp_mlTot cast a' by p]
                                                 terminates (interp_pml cast l' by cong <list *> p) by [IHx cast l' by cong <list *> p]) by plus_total
				{ (interp_pml x) = * }
			  trans cong (interp_pml *) x1
			  join (interp_pml (cons A' a' l'))
			       (plus (interp_ml cast a' by p) (interp_pml cast l' by cong <list *> p))
	end.

%- The first two elements of the argument to interp_pml are commutative -%
Define interp_pml_comm : Forall(x y:ml)(a:{x != (nil natp)})(b:{y != (nil natp)})(l:pml).
	{ (interp_pml (cons ml x (cons ml y l))) = (interp_pml (cons ml y (cons ml x l))) } :=
	induction (x:ml) by x1 x2 IHx return Forall(y:ml)(a:{x != (nil natp)})(b:{y != (nil natp)})(l:pml).
		{ (interp_pml (cons ml x (cons ml y l))) = (interp_pml (cons ml y (cons ml x l))) } with
		nil A' =>
			foralli(y:ml)(a:{x != (nil natp)})(b:{y != (nil natp)})(l:pml).
			contra trans symm x1 a
			{ (interp_pml (cons ml x (cons ml y l))) = (interp_pml (cons ml y (cons ml x l))) }
		| cons Ax' ax' lx' =>
			foralli(y:ml)(a:{x != (nil natp)})(b:{y != (nil natp)})(l:pml).
			abbrev p = symm inj <list *> x2 in
			trans cong (interp_pml (cons ml * (cons ml y l))) x1
			trans join (interp_pml (cons ml (cons Ax' ax' lx') (cons ml y l)))
				(plus (interp_ml (cons Ax' ax' lx')) (plus (interp_ml y) (interp_pml l)))
			existse [interp_mlTot (cons natp cast ax' by p    cast lx' by cong <list *> p)]
				foralli(mt1:nat) (mt1u:{ (interp_ml (cons natp cast ax' by p   cast lx' by cong <list *> p)) = mt1 }).
			existse [interp_mlTot y] foralli(mt2:nat) (mt2u:{ (interp_ml y) = mt2 }).
			existse [interp_pmlTot l] foralli(pmt:nat) (pmtu:{ (interp_pml l) = pmt }).
			trans cong (plus * (plus (interp_ml y) (interp_pml l))) mt1u
			trans cong (plus mt1 (plus * (interp_pml l))) mt2u
			trans cong (plus mt1 (plus mt2 *)) pmtu
			trans cong (plus mt1 *) [plus_comm mt2 pmt]
			trans symm [plus_assoc mt1 pmt mt2]
			existse [plus_total mt1 pmt] foralli(pt:nat) (ptu:{ (plus mt1 pmt) = pt }).
			trans cong (plus * mt2) ptu
			trans [plus_comm pt mt2]
			trans cong (plus mt2 *) symm ptu
			trans cong (plus * (plus mt1 pmt)) symm mt2u
			trans cong (plus (interp_ml y) (plus * pmt)) symm mt1u
			trans cong (plus (interp_ml y) (plus (interp_ml (cons Ax' ax' lx')) *)) symm pmtu
			trans cong (plus (interp_ml y) (plus (interp_ml *) (interp_pml l))) symm x1
			join (plus (interp_ml y) (plus (interp_ml x) (interp_pml l)))
				(interp_pml (cons ml y (cons ml x l)))
	end.

%- guru broken as of 10/25
Define fst_nate : Forall(n:natp).Exists(a:nat).{(fst nat nat n) = a} :=
  induction (n:natp) by n1 n2 IHn return Exists(a:nat).{ (fst nat nat n) = a } with
    mkpair nat nat a b => existsi a {(fst nat nat n) = *}
                                  trans cong (fst nat nat *) n1
                                        join (fst nat nat (mkpair nat nat a b)) a
  end.
-%

%-
Define interp_pml_plus : Forall(pml1 pml2:pml).{ (interp_pml (plusFF pml1 pml2)) = (plus (interp_pml pml1) (interp_pml pml2)) } :=
  induction (pml1:pml) by pml1' pml1'' IH1 return Forall(pml2:pml).{ (interp_pml (plusFF pml1 pml2)) = (plus (interp_pml pml1) (interp_pml pml2)) } with
    nil natp =>
      induction(pml2:pml) by pml2' pml2'' IH2 return { (interp_pml (plusFF pml1 pml2)) = (plus (interp_pml pml1) (interp_pml pml2)) } with
        nil natp =>        trans trans cong (interp_pml (plusFF * pml2)) pml1'
                                 trans cong (interp_pml (plusFF (nil natp) *)) pml2'
                                 trans cong (interp_pml *) trans join (plusFF (nil natp) (nil natp)) (append natp (nil natp) (nil natp))
                                                                 join (append natp (nil natp) (nil natp)) (nil natp)
                                       join (interp_pml (nil natp)) Z
                                 symm trans cong (plus (interp_pml *) (interp_pml pml2)) pml1'
                                      trans cong (plus * (interp_pml pml2)) join (interp_pml (nil natp)) Z
                                      trans cong (plus Z (interp_pml *)) pml2'
                                      trans cong (plus Z *) join (interp_pml (nil natp)) Z
                                            [plusZ Z]
      | cons natp h2 t2 => trans trans cong (interp_pml (plusFF * pml2)) pml1'
                                 trans cong (interp_pml (plusFF (nil natp) *)) pml2'
                                 trans cong (interp_pml *) join (plusFF (nil natp) (cons natp h2 t2)) (append ml (nil natp) (cons natp h2 t2))
                                 trans cong (interp_pml *) join (append ml (nil natp) (cons natp h2 t2)) (cons natp h2 t2)
                                       join (interp_pml (cons natp h2 t2)) (plus (interp_ml h2) (interp_pml t2))
                                 symm trans cong (plus (interp_pml *) (interp_pml pml2)) pml1'
                                      trans cong (plus * (interp_pml pml2)) join (interp_pml (nil natp)) Z
                                      trans join (plus Z (interp_pml pml2)) (interp_pml pml2)
                                      trans cong (interp_pml *) pml2'
                                            join (interp_pml (cons natp h2 t2)) (plus (interp_ml h2) (interp_pml t2))
      end
  | cons natp h1 t1 =>
      induction (pml2:pml) by pml2' pml2'' IH2 return { (interp_pml (plusFF pml1 pml2)) = (plus (interp_pml pml1) (interp_pml pml2)) } with
        nil natp =>        trans trans cong (interp_pml (plusFF * pml2)) pml1'
                                 trans cong (interp_pml (plusFF (cons natp h1 t1) *)) pml2'
                                 trans cong (interp_pml *) join (plusFF (cons natp h1 t1) (nil natp)) (append ml (cons natp h1 t1) (nil natp))
                                 trans cong (interp_pml *) join (append ml (cons natp h1 t1) (nil natp)) (cons natp h1 t1)
                                       join (interp_pml (cons natp h1 t1)) (plus (interp_ml h1) (interp_pml t1))
                                 symm trans cong (plus (interp_pml pml1) (interp_pml *)) pml2'
                                      trans cong (plus (interp_pml pml1) *) join (interp_pml (nil natp)) Z
                                      trans join (plus (interp_pml pml1) Z) (interp_pml pml1)
                                      trans cong (interp_pml *) pml1'
                                            join (interp_pml (cons natp h1 t1)) (plus (interp_ml h1) (interp_pml t1))
      | cons natp h2 t2 => trans trans cong (interp_pml (plusFF * pml2)) pml1'
                                 trans cong (interp_pml (plusFF (cons natp h1 t1) *)) pml2'
                                       cong (interp_pml *) join (plusFF (cons natp h1 t1) (cons natp h2 t2)) (append ml (cons natp h1 t1) (cons natp h2 t2))
% show (interp_pml (plusFF pml1 pml2)) =
                                 symm trans cong (plus (interp_pml *) (interp_pml pml2)) pml1'
                                      trans cong (plus (interp_pml (cons natp h1 t1)) (interp_pml *)) pml2'
                                            cong (plus * (interp_pml (cons natp h2 t2))) join (interp_pml (cons natp h1 t1)) (plus (interp_ml h1) (interp_pml t1))
% show (plus (interp_pml pml1) (interp_pml pml2)) = (plus (interp_ml h1) (interp_pml t1))
      end
  end.
-%

%-
Define flatten_interp_equiv : Forall(x:pme).{ (interp_pml (flatten x)) = (interp x) } :=
  induction (x:pme) by x1 x2 IHx return { (interp_pml (flatten x)) = (interp x) } with
    nate n =>      trans trans cong (interp_pml *) trans cong (flatten *) x1
                                                         join (flatten (nate n)) (cons ml (cons natp n (nil natp)) (nil ml))
                         trans join (interp_pml (cons ml (cons natp n (nil natp)) (nil ml))) (plus (interp_ml (cons natp n (nil natp))) (interp_pml (nil natp)))
                         trans cong (plus (interp_ml (cons natp n (nil natp))) *) join (interp_pml (nil natp)) Z
                         trans cong (plus * Z) trans join (interp_ml (cons natp n (nil natp))) (mult (fst nat nat n) (interp_ml (nil natp)))
                                               trans cong (mult (fst nat nat n) *) join (interp_ml (nil natp)) (S Z)
                                                     abbrev e1 = (fst nat nat n) in [mult_by_one e1] % INACTIVE error if I don't use abbrev
                               abbrev e1 = (fst nat nat n) in [plusZ e1] % INACTIVE error if I don't use abbrev
                         symm trans cong (interp *) x1
                                    join (interp (nate n)) (fst nat nat n)
  | pluse e1 e2 => trans       cong (interp_pml *) trans cong (flatten *) x1
                                                   trans join (flatten (pluse e1 e2)) (plusFF (flatten e1) (flatten e2))
                                                         join (plusFF (flatten e1) (flatten e2)) (append ml (flatten e1) (flatten e2))
                         symm trans cong (interp *) x1
                                    join (interp (pluse e1 e2)) (plus (interp e1) (interp e2))
  | multe e1 e2 => e2
  end.
-%

%% If interp is commutative in first two elts of list, and interp on non-nil is equiv to a Function taking hd l and (interp tl l)

%- interp_pml l for non-nil l is equivalent to a function taking (hd l) and (interp_pml tl l) -%
%-
Define interp_pml_equiv_fn : Forall(x:pml)(u:{x != (nil !)}).Exists(A B:type)(f:Fun(x:A)(y:B).nat).{(interp_pml x) = (f (hd x) (interp_pml (tl x)))} :=
  induction (x:pml) by x1 x2 IHx return Forall(u:{x != (nil !)}).Exists(A B:type)(f:Fun(x:A)(y:B).nat).{(interp_pml x) = (f (hd x) (interp_pml (tl x)))} with
    nil pml'      => foralli(u:{x != (nil !)}).contra trans symm x1 u Exists(A B:type)(f:Fun(x:A)(y:B).nat).{(interp_pml x) = (f (hd x) (interp_pml (tl x)))}
  | cons pml' h t => existsi ml
                             Exists(B:type)(f:Fun(x:*)(y:B).nat).{(interp_pml x) = (f (hd x) (interp_pml (tl x)))}
                             existsi nat
                                     Exists(f:Fun(x:ml)(y:*).nat).{(interp_pml x) = (f (hd x) (interp_pml (tl x)))}
                                     existsi (fun f(x:ml)(y:nat):nat.(plus (interp_ml x) y))
                                             {(interp_pml x) = (f (interp_ml (hd x)) (interp_pml (tl x)))}
                                             join h t
  end.
-%

% list_member: gives tt if x in l, ff otherwise
% list_member_append: list_member x (append l1 (cons x l2)) = tt
% list_member_append_iff: Forall({list_member x l = tt}).Exists(l1 l2).{ append l1 (cons x l2) = l }
% Forall(x l1 l2).{ list_member x merge l1 l2 = list_member x append l1 l2 }


Define foldr_pf : Forall(A B:type)
                        (f:Fun(owned a:A)(b:B).B)
                        (b:B)
                        (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr A B f b (append A l1 (cons A a l2))) = (foldr A B f b (cons A a (append A l1 l2))) })
                        (cmp:Fun(x y : A).bool)
                        (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b })
                        (l1 l2:<list A>).
                    { (foldr A B f b (append A l1 l2)) = (foldr A B f b (merge A l1 l2 cmp)) } :=
  foralli(A B:type)
         (f:Fun(owned a:A)(b:B).B)
         (b:B)
         (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr A B f b (append A l1 (cons A a l2))) = (foldr A B f b (cons A a (append A l1 l2))) })
         (cmp:Fun(x y : A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>).{ (foldr A B f b (append A l1 l2)) = (foldr A B f b (merge A l1 l2 cmp)) } with
      nil A' =>
        induction(l2:<list A>) by l2p l2t IHl2 return { (foldr A B f b (append A l1 l2)) = (foldr A B f b (merge A l1 l2 cmp)) } with
          nil A'' =>
            cong (foldr A B f b *)
                 trans cong (append A * l2) l1p
                 trans cong (append A (nil A) *) l2p
                 trans join (append A (nil A) (nil A))
                            (merge A (nil A) (nil A) cmp)
                 trans cong (merge A * (nil A) cmp) symm l1p
                       cong (merge A l1 * cmp) symm l2p
        | cons A'' h' t' =>
            cong (foldr A B f b *)
                 trans cong (append A * l2) l1p
                 trans cong (append A (nil A) *) l2p
                 trans join (append A (nil A) (cons A'' h' t'))
                            (merge A (nil A) (cons A'' h' t') cmp)
                 trans cong (merge A * (cons A'' h' t') cmp) symm l1p
                       cong (merge A l1 * cmp) symm l2p
        end
    | cons A' h t =>
        induction(l2:<list A>) by l2p l2t IHl2 return { (foldr A B f b (append A l1 l2)) = (foldr A B f b (merge A l1 l2 cmp)) } with
          nil A'' =>
            cong (foldr A B f b *)
                 trans cong (append A * l2) l1p
                 trans cong (append A (cons A' h t) *) l2p
                 trans [append_nil A' (cons A' h t)]
                 trans join (cons A' h t)
                            (merge A (cons A' h t) (nil A'') cmp)
                 trans cong (merge A * (nil A'') cmp) symm l1p
                       cong (merge A l1 * cmp) symm l2p
        | cons A'' h' t' =>
            existse [cmp_total cast h by symm inj <list *> l1t cast h' by symm inj <list *> l2t]
                    induction(c:bool) by cp ct IHc return Forall(u:{ (cmp h h') = c }).{ (foldr A B f b (append A l1 l2)) = (foldr A B f b (merge A l1 l2 cmp)) } with
                      ff =>
                        foralli(u:{ (cmp h h') = c }).
                          trans cong (foldr A B f b *)
                                     trans cong (append A * l2) l1p
                                           join (append A (cons A' h t) l2)
                                                (cons A h (append A t l2))
                          trans join (foldr A B f b (cons A h (append A t l2)))
                                     (f h (foldr A B f b (append A t l2)))
                          symm trans cong (foldr A B f b *)
                                     trans cong (merge A * l2 cmp) l1p
                                     trans cong (merge A (cons A' h t) * cmp) l2p
                                     trans join (merge A (cons A' h t) (cons A'' h' t') cmp)
                                                match (cmp h h') by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                     trans cong match * by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                                trans u cp
                                           join match ff by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                                (cons A h (merge A t (cons A'' h' t') cmp))
                               trans join (foldr A B f b (cons A h (merge A t (cons A'' h' t') cmp)))
                                          (f h (foldr A B f b (merge A t (cons A'' h' t') cmp)))
                               trans cong (f h (foldr A B f b (merge A t * cmp)))
                                          symm l2p
                                     cong (f h *)
                                          symm [IHl1 cast t by cong <list *> symm inj <list *> l1t l2]
                    | tt =>
                        foralli(u:{ (cmp h h') = c }).
                          trans cong (foldr A B f b (append A l1 *)) l2p

%%         (fcomm:Forall(a:A)(l1 l2:<list A>).{ (foldr A B f b (append A l1 l2)) = (foldr A B f b (append A l1 l2)) })
%%         (foldr A B f b (append A l1 (cons A'' h' t'))) = 
                          trans [fcomm cast h' by symm inj <list *> l2t b l1 cast t' by cong <list *> symm inj <list *> l2t]
                          trans join (foldr A B f b (cons A h' (append A l1 t')))
                                     (f h' (foldr A B f b (append A l1 t')))
                          symm trans cong (foldr A B f b *)
                                     trans cong (merge A * l2 cmp) l1p
                                     trans cong (merge A (cons A' h t) * cmp) l2p
                                     trans join (merge A (cons A' h t) (cons A'' h' t') cmp)
                                                match (cmp h h') by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                     trans cong match * by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                                trans u cp
                                           join match tt by u v return <list A> with
                                                  ff => (cons A h (merge A t (cons A'' h' t') cmp))
                                                | tt => (cons A h' (merge A (cons A' h t) t' cmp))
                                                end
                                                (cons A h' (merge A (cons A' h t) t' cmp))
                               trans join (foldr A B f b (cons A h' (merge A (cons A' h t) t' cmp)))
                                          (f h' (foldr A B f b (merge A (cons A' h t) t' cmp)))
                               trans cong (f h' (foldr A B f b (merge A * t' cmp)))
                                          symm l1p
                                     cong (f h' *)
                                          symm [IHl2 cast t' by cong <list *> symm inj <list *> l2t]
           end
        end
    end.

Define foldr_pf2n : Forall(A B:type)
                          (f:Fun(owned a:A)(b:B).B)
                          (n:nat)
                          (l:<list A>)
                          (nlen:{ (le (list_length ! l) n) = tt })
                          (b:B)
                          (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                          (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                          (cmp:Fun(x y:A).bool)
                          (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                      { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } :=
  foralli(A B:type)
         (f:Fun(owned a:A)(b:B).B).
    induction(n:nat) by np nt IHn return Forall(l:<list A>)
                                               (nlen:{ (le (list_length ! l) n) = tt })
                                               (b:B)
                                               (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                                               (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                                               (cmp:Fun(x y:A).bool)
                                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                           { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } with
      Z =>
        induction(l:<list A>) by lp lt_ IHl return Forall(nlen:{ (le (list_length ! l) n) = tt })
                                                         (b:B)
                                                         (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                                                         (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                                                         (cmp:Fun(x y:A).bool)
                                                         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                     { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } with
          nil A' =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (b:B)
                   (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                   (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              hypjoin (foldr ! ! f b l)
                      (foldr ! ! f b (msort A l cmp))
                   by lp end
        | cons A' h t =>
            foralli(nlen:{ (le (list_length ! l) n) = tt }).
              contra trans symm nlen
                     trans hypjoin (le (list_length ! l) n)
                                   ff
                                by np lp end
                           clash ff tt
                Forall(b:B)
                      (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                      (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                      (cmp:Fun(x y:A).bool)
                      (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                  { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) }
        end
    | S n' =>
        induction(l:<list A>) by lp lt_ IHl return Forall(nlen:{ (le (list_length ! l) n) = tt })
                                                         (b:B)
                                                         (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                                                         (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                                                         (cmp:Fun(x y:A).bool)
                                                         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                     { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } with
          nil A' =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (b:B)
                   (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                   (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
            abbrev nlen' = trans cong (le (list_length ! *) n') lp
                           trans join (le (list_length ! (nil !)) n')
                                      (le Z n')
                                 [Z_le n'] in
            [IHn n' l nlen' b fcomm ftot cmp cmp_total]
        | cons A' h t =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (b:B)
                   (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                   (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              [ induction(ll_lt_nv:bool) by ll_lt_nvp ll_lt_nvt IHll_lt_nv return Forall(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                                                                                    { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } with
                  ff =>
                    foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                      abbrev l1 = terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot in
                      abbrev l2 = terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot in

                      abbrev ll_lt_nff = trans ll_lt_n_pf ll_lt_nvp in
                      abbrev ll_eq_n = [eqnatEq terminates (list_length ! l) by list_length_total n
                                                symm trans symm nlen
                                                     trans join (le (list_length ! l) n)
                                                                (or (lt (list_length ! l) n) (eqnat (list_length ! l) n))
                                                     trans cong (or * (eqnat (list_length ! l) n)) ll_lt_nff
                                                           join (or ff (eqnat (list_length ! l) n))
                                                                (eqnat (list_length ! l) n)] in

                      abbrev hcast = cast h by symm inj <list *> lt_ in
                      abbrev tcast = cast t by cong <list *> symm inj <list *> lt_ in

                      [ induction(_tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = _tt }).
                                                                         { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } with
                          nil A'' =>
                            foralli(ttpf:{ t = _tt }).
                              % l = (cons ! h (nil !))
                              abbrev lfullp = trans lp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in
                              cong (foldr ! ! f b *)
                                   trans lfullp
                                   trans join (cons ! h (nil !))
                                              (msort ! (cons ! h (nil !)) cmp)
                                         cong (msort ! * cmp) symm lfullp
                        | cons A'' h' t' =>
                            abbrev h'cast = cast h' by symm inj <list *> ttt in
                            abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in
                            foralli(ttpf:{ t = _tt }).
                              % l = (cons ! h (cons ! h' t'))
                              abbrev lfullp = trans lp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                              abbrev lne = trans lp clash (cons ! h t) (nil !) in
                              abbrev lnne = foralli(x:A).trans lfullp [list_not_length_1 A hcast h'cast t'cast x] in

                              abbrev lne1' = [split_list_nonnil_fst A l lne lnne] in
                              abbrev nlen1' = [le_trans terminates (list_length A l1) by list_length_total
                                                        terminates (list_length A l) by list_length_total
                                                        n
                                                        [split_list_le_fst A l]
                                                        nlen] in
                              abbrev lne2' = [split_list_nonnil_snd A l lne] in
                              abbrev nlen2' = [le_trans terminates (list_length A l2) by list_length_total
                                                        terminates (list_length A l) by list_length_total
                                                        n
                                                        [split_list_le_snd A l]
                                                        nlen] in

                              abbrev ih1 = [IHn n l1 nlen1' terminates (foldr A B f b terminates (msort A l2 cmp) by [msort_total A l2 cmp cmp_total])
                                                                    by [foldrTot A B f ftot b terminates (msort A l2 cmp) by [msort_total A l2 cmp cmp_total]]
                                                            fcomm ftot cmp cmp_total] in
                              abbrev ih2 = [IHn n l2 nlen2' b fcomm ftot cmp cmp_total] in

                              abbrev m1 = (msort A l1 cmp) in
                              abbrev m2 = (msort A l2 cmp) in

                              trans cong (foldr ! ! f b *)
                                         trans symm [append_split_list A l]
                                               [append_appendf A l1 l2]
                              trans [foldr_appendf A B f b l1 l2]
                              trans cong (foldr ! ! f * l1)
                                         ih2
                              trans ih1
                              trans symm [foldr_appendf A B f b m1 m2]
                              trans cong (foldr ! ! f b *)
                                         [appendf_append A m1 m2]
                              trans [foldr_pf A B f b fcomm cmp cmp_total m1 m2]
                              trans join (foldr ! ! f b (merge ! m1 m2 cmp))
                                         (foldr ! ! f b (merge ! (msort ! (fst ! ! (split_list ! l)) cmp) (msort ! (snd ! ! (split_list ! l)) cmp) cmp))
                              trans cong (foldr ! ! f b (merge ! (msort ! (fst ! ! (split_list ! *)) cmp) (msort ! (snd ! ! (split_list ! *)) cmp) cmp))
                                         lfullp
                              trans join (foldr ! ! f b (merge ! (msort ! (fst ! ! (split_list ! (cons ! h (cons ! h' t')))) cmp)
                                                                 (msort ! (snd ! ! (split_list ! (cons ! h (cons ! h' t')))) cmp) cmp))
                                         (foldr ! ! f b (msort ! (cons ! h (cons ! h' t')) cmp))
                                    cong (foldr ! ! f b (msort ! * cmp))
                                         symm  lfullp
                        end tcast join t t ]
                | tt =>
                    foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                      abbrev ll_lt_n = trans ll_lt_n_pf ll_lt_nvp in
                      abbrev nlen' = [lt_pred n' n terminates (list_length A l) by list_length_total np ll_lt_n] in
                      [IHn n' l nlen' b fcomm ftot cmp cmp_total]
                end terminates (lt terminates (list_length A l) by list_length_total n) by lt_total
                    join (lt (list_length ! l) n) (lt (list_length ! l) n) ]
        end
    end.

Define foldr_pf2 : Forall(A B:type)
                         (f:Fun(owned a:A)(b:B).B)
                         (l:<list A>)
                         (b:B)
                         (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
                         (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
                         (cmp:Fun(x y:A).bool)
                         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                     { (foldr ! ! f b l) = (foldr ! ! f b (msort ! l cmp)) } :=
  foralli(A B:type)
         (f:Fun(owned a:A)(b:B).B)
         (l:<list A>)
         (b:B)
         (fcomm:Forall(a:A)(b:B)(l1 l2:<list A>).{ (foldr ! ! f b (append ! l1 (cons ! a l2))) = (foldr ! ! f b (cons ! a (append ! l1 l2))) })
         (ftot:Forall(a:A)(b:B).Exists(c:B).{ (f a b) = c })
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev n = (list_length A l) in
    abbrev nlen = [x_le_x terminates (list_length A l) by list_length_total] in
    [foldr_pf2n A B f n l nlen b fcomm ftot cmp cmp_total].

Define strengthen_comm : Forall(A B:type)
                               (x:A)
                               (l1 l2:<list A>)
                               (f:Fun(owned x:A)(y:B).B)
                               (b:B)
                               (fcomm:Forall(b:B)(a1 a2:A).{ (f a2 (f a1 b)) = (f a1 (f a2 b)) })
                               (ftot:Forall(x:A)(y:B).Exists(z:B).{ (f x y) = z }).
                           { (foldr ! ! f b (append ! l1 (cons ! x l2))) = (foldr ! ! f b (cons ! x (append ! l1 l2))) } :=
  foralli(A B:type)
         (x:A).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)
                                                        (f:Fun(owned x:A)(y:B).B)
                                                        (b:B)
                                                        (fcomm:Forall(b:B)(a1 a2:A).{ (f a2 (f a1 b)) = (f a1 (f a2 b)) })
                                                        (ftot:Forall(x:A)(y:B).Exists(z:B).{ (f x y) = z }).
                                                    { (foldr ! ! f b (append ! l1 (cons ! x l2))) = (foldr ! ! f b (cons ! x (append ! l1 l2))) } with
      nil A1 =>
        foralli(l2:<list A>)
               (f:Fun(owned x:A)(y:B).B)
               (b:B)
               (fcomm:Forall(b:B)(a1 a2:A).{ (f a2 (f a1 b)) = (f a1 (f a2 b)) })
               (ftot:Forall(x:A)(y:B).Exists(z:B).{ (f x y) = z }).
          hypjoin (foldr ! ! f b (append ! l1 (cons ! x l2)))
                  (foldr ! ! f b (cons ! x (append ! l1 l2)))
               by l1p end
    | cons A1 h1 t1 =>
        abbrev h1cast = cast h1 by symm inj <list *> l1t in
        abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
        foralli(l2:<list A>)
               (f:Fun(owned x:A)(y:B).B)
               (b:B)
               (fcomm:Forall(b:B)(a1 a2:A).{ (f a2 (f a1 b)) = (f a1 (f a2 b)) })
               (ftot:Forall(x:A)(y:B).Exists(z:B).{ (f x y) = z }).
          abbrev ih = [IHl1 t1cast l2 f b fcomm ftot] in
          hypjoin (foldr ! ! f b (append ! l1 (cons ! x l2)))
                  (foldr ! ! f b (cons ! x (append ! l1 l2)))
               by l1p ih [fcomm terminates (foldr A B f b terminates (append A t1cast l2) by append_total)
                                        by [foldrTot A B f ftot b terminates (append A t1cast l2) by append_total]
                                x h1cast] end
    end.

Define interp_mlf_f_total : Forall(x:natp)(y:nat).Exists(o:nat).{ (interp_mlf_f x y) = o } :=
  foralli(x:natp)(y:nat).
    existse [mult_total terminates (fst nat nat x) by fstTot y]
      foralli(o:nat)(opf:{ (mult (fst ! ! x) y) = o }).
        existsi o
                { (interp_mlf_f x y) = * }
          trans join (interp_mlf_f x y)
                     (mult (fst ! ! x) y)
                opf.

Define interp_mlf_total : Forall(x:ml).Exists(n:nat).{ (interp_mlf x) = n } :=
  induction(x:ml) by xp xt IHx return Exists(n:nat).{ (interp_mlf x) = n } with
    nil A =>
      existsi (S Z)
              { (interp_mlf x) = * }
        trans cong (interp_mlf *) xp
              join (interp_mlf (nil !))
                   (S Z)
  | cons A h t =>
      abbrev hcast = cast h by symm inj <list *> xt in
      abbrev tcast = cast t by cong <list *> symm inj <list *> xt in
      abbrev f = interp_mlf_f in
      abbrev ftot = interp_mlf_f_total in
      existse [IHx tcast]
        foralli(n':nat)(n'pf:{ (interp_mlf t) = n' }).
          existsi terminates (f hcast n') by ftot
                  { (interp_mlf x) = * }
            trans cong (interp_mlf *) xp
            trans join (interp_mlf (cons ! h t))
                       (f h (interp_mlf t))
                  cong (f h *) n'pf
  end.

Define interp_pmlf_f_total : Forall(x:ml)(y:nat).Exists(o:nat).{ (interp_pmlf_f x y) = o } :=
  foralli(x:ml)(y:nat).
    existse [plus_total terminates (interp_mlf x) by interp_mlf_total y]
      foralli(o:nat)(opf:{ (plus (interp_mlf x) y) = o }).
        existsi o
                { (interp_pmlf_f x y) = * }
          trans join (interp_pmlf_f x y)
                     (plus (interp_mlf x) y)
                opf.

Define interp_pmlf_total : Forall(x:pml).Exists(n:nat).{ (interp_pmlf x) = n } :=
  abbrev f = interp_pmlf_f in
  abbrev ftot = interp_pmlf_f_total in
  foralli(x:pml).
    existse [foldrTot ml nat f ftot Z x]
      foralli(m:nat)(mpf:{ (foldr ! ! f Z x) = m }).
        existsi m
                { (interp_pmlf x) = * }
          trans join (interp_pmlf x)
                     (foldr ! ! f Z x)
                mpf.

Define interp_mlf_comm : Forall(x:natp)
                               (n:nat)
                               (l1 l2:ml).
                           { (foldr ! ! interp_mlf_f n (append ! l1 (cons ! x l2))) = (foldr ! ! interp_mlf_f n (cons ! x (append ! l1 l2))) } :=
  foralli(x:natp)
         (n:nat)
         (l1 l2:ml).
    abbrev f = interp_mlf_f in
    abbrev fcomm = foralli(y:nat)(x1 x2:natp).%% show (f x2 (f x1 y)) = (f x1 (f x2 y))
                     trans join (f x2 (f x1 y))
                                (mult (fst ! ! x2) (mult (fst ! ! x1) y))
                     trans symm [mult_assoc terminates (fst nat nat x2) by fstTot
                                            terminates (fst nat nat x1) by fstTot
                                            y]
                     trans cong (mult * y)
                                [mult_comm terminates (fst nat nat x2) by fstTot
                                           terminates (fst nat nat x1) by fstTot]
                     trans [mult_assoc terminates (fst nat nat x1) by fstTot
                                       terminates (fst nat nat x2) by fstTot
                                       y]
                           join (mult (fst ! ! x1) (mult (fst ! ! x2) y))
                                (f x1 (f x2 y)) in
    abbrev ftot = interp_mlf_f_total in
    hypjoin (foldr ! ! interp_mlf_f n (append ! l1 (cons ! x l2)))
            (foldr ! ! interp_mlf_f n (cons ! x (append ! l1 l2)))
         by [strengthen_comm natp nat x l1 l2 interp_mlf_f n fcomm ftot] end.

Define interp_pmlf_comm : Forall(x:ml)
                                (n:nat)
                                (l1 l2:pml).
                            { (foldr ! ! interp_pmlf_f n (append ! l1 (cons ! x l2))) = (foldr ! ! interp_pmlf_f n (cons ! x (append ! l1 l2))) } :=
  foralli(x:ml)
         (n:nat)
         (l1 l2:pml).
    abbrev f = interp_pmlf_f in
    abbrev fcomm = foralli(y:nat)(x1 x2:ml).%% show (f x2 (f x1 y)) = (f x1 (f x2 y))
                     trans join (f x2 (f x1 y))
                                (plus (interp_mlf x2) (plus (interp_mlf x1) y))
                     trans symm [plus_assoc terminates (interp_mlf x2) by interp_mlf_total
                                            terminates (interp_mlf x1) by interp_mlf_total
                                            y]
                     trans cong (plus * y)
                                [plus_comm terminates (interp_mlf x2) by interp_mlf_total
                                           terminates (interp_mlf x1) by interp_mlf_total]
                     trans [plus_assoc terminates (interp_mlf x1) by interp_mlf_total
                                       terminates (interp_mlf x2) by interp_mlf_total
                                       y]
                           join (plus (interp_mlf x1) (plus (interp_mlf x2) y))
                                (f x1 (f x2 y)) in
    abbrev ftot = interp_pmlf_f_total in
    hypjoin (foldr ! ! interp_pmlf_f n (append ! l1 (cons ! x l2)))
            (foldr ! ! interp_pmlf_f n (cons ! x (append ! l1 l2)))
         by [strengthen_comm ml nat x l1 l2 interp_pmlf_f n fcomm ftot] end.

Define cmp_natp_total : Forall(x y:natp).Exists(z:bool).{ (cmp_natp x y) = z } :=
  foralli(x y:natp).
    existse [le_total terminates (snd nat nat x) by sndTot
                      terminates (snd nat nat y) by sndTot]
      foralli(z:bool)(zpf:{ (le (snd ! ! x) (snd ! ! y)) = z }).
        existsi z
                { (cmp_natp x y) = * }
          trans join (cmp_natp x y)
                     (le (snd ! ! x) (snd ! ! y))
                zpf.

Define cmp_ml_total : Forall(x y:ml).Exists(z:bool).{ (cmp_ml x y) = z } :=
  induction(x:ml) by xp xt IHx return Forall(y:ml).Exists(z:bool).{ (cmp_ml x y) = z } with
    nil Ax =>
      foralli(y:ml).
        existsi tt
                { (cmp_ml x y) = * }
          hypjoin (cmp_ml x y)
                  tt
               by xp end
  | cons Ax x1 x2 =>
      induction(y:ml) by yp yt IHy return Exists(z:bool).{ (cmp_ml x y) = z } with
        nil Ay =>
          existsi ff
                  { (cmp_ml x y) = * }
            hypjoin (cmp_ml x y)
                    ff
                 by xp yp end
      | cons Ay y1 y2 =>
          abbrev x1cast = cast x1 by symm inj <list *> xt in
          abbrev x2cast = cast x2 by cong <list *> symm inj <list *> xt in
          abbrev y1cast = cast y1 by symm inj <list *> yt in
          abbrev y2cast = cast y2 by cong <list *> symm inj <list *> yt in
          [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat (snd ! ! x1) (snd ! ! y1)) = z }).Exists(z:bool).{ (cmp_ml x y) = z } with
              ff =>
                foralli(zpf:{ (eqnat (snd ! ! x1) (snd ! ! y1)) = z }).
                  existse [lt_total terminates (snd nat nat x1cast) by sndTot
                                    terminates (snd nat nat y1cast) by sndTot]
                    foralli(zz:bool)(zzpf:{ (lt (snd ! ! x1) (snd ! ! y1)) = zz }).
                      existsi zz
                              { (cmp_ml x y) = * }
                        trans hypjoin (cmp_ml x y)
                                      (lt (snd ! ! x1) (snd ! ! y1))
                                   by xp
                                      yp
                                      trans zpf zp end
                              zzpf
            | tt =>
                foralli(zpf:{ (eqnat (snd ! ! x1) (snd ! ! y1)) = z }).
                  existse [IHx x2cast y2cast]
                    foralli(zz:bool)(zzpf:{ (cmp_ml x2 y2) = zz }).
                      existsi zz
                              { (cmp_ml x y) = * }
                        trans hypjoin (cmp_ml x y)
                                      (cmp_ml x2 y2)
                                   by xp
                                      yp
                                      trans zpf zp end
                              zzpf
            end terminates (eqnat terminates (snd nat nat x1cast) by sndTot
                                  terminates (snd nat nat y1cast) by sndTot) by eqnatTot
                join (eqnat (snd ! ! x1) (snd ! ! y1)) (eqnat (snd ! ! x1) (snd ! ! y1)) ]
      end
  end.

Define ml_canon_equality : Forall(x:ml).{ (interp_mlf x) = (interp_mlf (msort ! x cmp_natp)) } :=
  abbrev f = interp_mlf_f in
  abbrev fcomm = foralli(y:nat)(x1 x2:natp).%% show (f x2 (f x1 y)) = (f x1 (f x2 y))
                   trans join (f x2 (f x1 y))
                              (mult (fst ! ! x2) (mult (fst ! ! x1) y))
                   trans symm [mult_assoc terminates (fst nat nat x2) by fstTot
                                          terminates (fst nat nat x1) by fstTot
                                          y]
                   trans cong (mult * y)
                              [mult_comm terminates (fst nat nat x2) by fstTot
                                         terminates (fst nat nat x1) by fstTot]
                   trans [mult_assoc terminates (fst nat nat x1) by fstTot
                                     terminates (fst nat nat x2) by fstTot
                                     y]
                         join (mult (fst ! ! x1) (mult (fst ! ! x2) y))
                              (f x1 (f x2 y)) in
  abbrev ftot = interp_mlf_f_total in
  foralli(x:ml).
    hypjoin (interp_mlf x)
            (interp_mlf (msort ! x cmp_natp))
         by [foldr_pf2 natp nat interp_mlf_f x (S Z) interp_mlf_comm ftot cmp_natp cmp_natp_total] end.

Define pml_canon_equality : Forall(x:pml).{ (interp_pmlf x) = (interp_pmlf (msort ! x cmp_ml)) } :=
  abbrev f = interp_pmlf_f in
  abbrev fcomm = foralli(y:nat)(x1 x2:ml).%% show (f x2 (f x1 y)) = (f x1 (f x2 y))
                   trans join (f x2 (f x1 y))
                              (plus (interp_mlf x2) (plus (interp_mlf x1) y))
                   trans symm [plus_assoc terminates (interp_mlf x2) by interp_mlf_total
                                          terminates (interp_mlf x1) by interp_mlf_total
                                          y]
                   trans cong (plus * y)
                              [plus_comm terminates (interp_mlf x2) by interp_mlf_total
                                         terminates (interp_mlf x1) by interp_mlf_total]
                   trans [plus_assoc terminates (interp_mlf x1) by interp_mlf_total
                                     terminates (interp_mlf x2) by interp_mlf_total
                                     y]
                         join (plus (interp_mlf x1) (plus (interp_mlf x2) y))
                              (f x1 (f x2 y)) in
  abbrev ftot = interp_pmlf_f_total in
  foralli(x:pml).
    hypjoin (interp_pmlf x)
            (interp_pmlf (msort ! x cmp_ml))
         by [foldr_pf2 ml nat interp_pmlf_f x Z interp_pmlf_comm ftot cmp_ml cmp_ml_total] end.

Define sort_pml_helper_total : Forall(x:pml).Exists(y:pml).{ (sort_pml_helper x) = y } :=
  induction(x:pml) by xp xt IHx return Exists(y:pml).{ (sort_pml_helper x) = y } with
    nil A' =>
      existsi x
              { (sort_pml_helper x) = * }
        hypjoin (sort_pml_helper x)
                x
             by xp end
  | cons A' a' l' =>
      abbrev a'cast = cast a' by symm inj <list *> xt in
      abbrev l'cast = cast l' by cong <list *> symm inj <list *> xt in
      existse [IHx l'cast]
        foralli(yy:pml)(yypf:{ (sort_pml_helper l') = yy }).
          existsi (cons ml terminates (msort natp a'cast cmp_natp) by [msort_total natp a'cast cmp_natp cmp_natp_total] yy)
                  { (sort_pml_helper x) = * }
            hypjoin (sort_pml_helper x)
                    (cons ml (msort natp a' cmp_natp) yy)
                 by xp yypf end
  end.

Define sort_pml_total : Forall(x:pml).Exists(y:pml).{ (sort_pml x) = y } :=
  induction(x:pml) by xp xt IHx return Exists(y:pml).{ (sort_pml x) = y } with
    nil A' =>
      existsi x
              { (sort_pml x) = * }
        hypjoin (sort_pml x)
                x
             by xp end
  | cons A' a' l' =>
      existsi terminates (msort ml terminates (sort_pml_helper x) by sort_pml_helper_total cmp_ml)
                      by [msort_total ml terminates (sort_pml_helper x) by sort_pml_helper_total cmp_ml cmp_ml_total]
              { (sort_pml x) = * }
        trans cong (sort_pml *) xp
        trans join (sort_pml (cons ! a' l'))
                   (msort ml (sort_pml_helper (cons ! a' l')) cmp_ml)
              cong (msort ml (sort_pml_helper *) cmp_ml) symm xp
  end.

Define sorted_interp_equiv : Forall(x:pml).
                               { (interp_pmlf x) = (interp_pmlf (sort_pml x)) } :=
  induction(x:pml) by xp xt IHx return { (interp_pmlf x) = (interp_pmlf (sort_pml x)) } with
    nil A =>
      hypjoin (interp_pmlf x)
              (interp_pmlf (sort_pml x))
           by xp end
  | cons A h t =>
      abbrev hcast = cast h by symm inj <list *> xt in
      abbrev tcast = cast t by cong <list *> symm inj <list *> xt in
      abbrev p1 = trans cong (interp_pmlf *) xp
                  trans join (interp_pmlf (cons ! h t))
                             (plus (interp_mlf h) (interp_pmlf t))
                        cong (plus (interp_mlf h) *)
                             [IHx tcast] in
      abbrev p2 = trans cong (interp_pmlf (sort_pml *)) xp
                  trans join (interp_pmlf (sort_pml (cons ! h t)))
                             (interp_pmlf (msort ml (cons ml (msort natp h cmp_natp) (sort_pml_helper t)) cmp_ml))
                  trans symm [pml_canon_equality (cons ml terminates (msort natp hcast cmp_natp) by [msort_total natp hcast cmp_natp cmp_natp_total]
                                                          terminates (sort_pml_helper tcast) by sort_pml_helper_total)]
                  trans join (interp_pmlf (cons ml (msort natp h cmp_natp) (sort_pml_helper t)))
                             (plus (interp_mlf (msort natp h cmp_natp)) (interp_pmlf (sort_pml_helper t)))
                  trans cong (plus * (interp_pmlf (sort_pml_helper t)))
                             symm [ml_canon_equality hcast]
                        cong (plus (interp_mlf h) *)
                             [pml_canon_equality terminates (sort_pml_helper tcast) by sort_pml_helper_total] in
      [ induction(tt:pml) by ttp ttt IHtt return Forall(ttpf:{ t = tt }).
                                                   { (interp_pmlf x) = (interp_pmlf (sort_pml x)) } with
          nil A' =>
            foralli(ttpf:{ t = tt }).
              trans p1
                    symm trans p2
                               cong (plus (interp_mlf h) (interp_pmlf *))
                                    hypjoin (msort ! (sort_pml_helper t) cmp_ml)
                                            (sort_pml t)
                                         by trans ttpf ttp end
        | cons A' h' t' =>
            foralli(ttpf:{ t = tt }).
              trans p1
                    symm trans p2
                               cong (plus (interp_mlf h) (interp_pmlf *))
                                    symm trans cong (sort_pml *)
                                                    trans ttpf ttp
                                         trans join (sort_pml (cons ! h' t'))
                                                    (msort ! (sort_pml_helper (cons ! h' t')) cmp_ml)
                                               cong (msort ! (sort_pml_helper *) cmp_ml)
                                                    symm trans ttpf ttp
        end tcast join t t ]
  end.

Define plusFF_total : Forall(x y:pml).Exists(z:pml).{ (plusFF x y) = z } :=
  foralli(x y:pml).
    existse [append_total ml x y]
      foralli(z:pml)(zpf:{ (append ! x y) = z }).
        existsi z
                { (plusFF x y) = * }
          hypjoin (plusFF x y)
                  z
               by zpf end.

Define multTT_total : Forall(x y:ml).Exists(z:ml).{ (multTT x y) = z } :=
  foralli(x y:ml).
    existsi terminates (append natp x y) by append_total
            { (multTT x y) = * }
      join (multTT x y)
           (append ! x y).

Define multFT_total : Forall(x:pml)(y:ml).Exists(z:pml).{ (multFT x y) = z } :=
  induction(x:pml) by xp xt IHx return Forall(y:ml).Exists(z:pml).{ (multFT x y) = z } with
    nil A' =>
      foralli(y:ml).
        existsi x
                { (multFT x y) = * }
          hypjoin (multFT x y)
                  x
               by xp end
  | cons A' a' l' =>
      abbrev a'cast = cast a' by symm inj <list *> xt in
      abbrev l'cast = cast l' by cong <list *> symm inj <list *> xt in
      foralli(y:ml).
        existse [IHx l'cast y]
          foralli(zz:pml)(zzpf:{ (multFT l' y) = zz }).
            existsi (cons ml terminates (multTT a'cast y) by multTT_total zz)
                    { (multFT x y) = * }
              hypjoin (multFT x y)
                      (cons ml terminates (multTT a' y) by multTT_total zz)
                   by xp zzpf end
  end.

Define multFF_total : Forall(x y:pml).Exists(z:pml).{ (multFF x y) = z } :=
  induction(x:pml) by xp xt IHx return Forall(y:pml).Exists(z:pml).{ (multFF x y) = z } with
    nil Ax' =>
      foralli(y:pml).
        existsi (nil ml)
                { (multFF x y) = * }
          hypjoin (multFF x y)
                  (nil !)
               by xp end
  | cons Ax' ax' lx' =>
      induction(y:pml) by yp yt IHy return Exists(z:pml).{ (multFF x y) = z } with
        nil Ay' =>
          existsi (nil ml)
                  { (multFF x y) = * }
            hypjoin (multFF x y)
                    (nil !)
                 by xp yp end
      | cons Ay' ay' ly' =>
          abbrev ay'cast = cast ay' by symm inj <list *> yt in
          abbrev ly'cast = cast ly' by cong <list *> symm inj <list *> yt in
          existse [IHy ly'cast]
            foralli(zz:pml)(zzpf:{ (multFF x ly') = zz }).
              existsi terminates (plusFF terminates (multFT x ay'cast) by multFT_total zz) by plusFF_total
                      { (multFF x y) = * }
                trans hypjoin (multFF x y)
                              (plusFF (multFT x ay') (multFF x ly'))
                           by xp yp end
                      cong (plusFF (multFT x ay') *) zzpf
      end
  end.

Define flatten_total : Forall(x:pme).Exists(y:pml).{ (flatten x) = y } :=
  induction(x:pme) by xp xt IHx return Exists(y:pml).{ (flatten x) = y } with
    nate n =>
      existsi (cons ml (cons natp n (nil natp)) (nil ml))
              { (flatten x) = * }
        hypjoin (flatten x)
                (cons ! (cons ! n (nil !)) (nil !))
             by xp end
  | pluse e1 e2 =>
      existse [IHx e1]
        foralli(f1:pml)(f1pf:{ (flatten e1) = f1 }).
          existse [IHx e2]
            foralli(f2:pml)(f2pf:{ (flatten e2) = f2 }).
              existsi terminates (plusFF f1 f2) by plusFF_total
                      { (flatten x) = * }
                hypjoin (flatten x)
                        (plusFF f1 f2)
                     by xp f1pf f2pf end
  | multe e1 e2 =>
      existse [IHx e1]
        foralli(f1:pml)(f1pf:{ (flatten e1) = f1 }).
          existse [IHx e2]
            foralli(f2:pml)(f2pf:{ (flatten e2) = f2 }).
              existsi terminates (multFF f1 f2) by multFF_total
                      { (flatten x) = * }
                hypjoin (flatten x)
                        (multFF f1 f2)
                     by xp f1pf f2pf end
  end.

Define interp_mlf_mult : Forall(b:nat)(x:ml).{ (foldr ! ! interp_mlf_f b x) = (mult (interp_mlf x) b) } :=
  %% We need induction on b because the nil cases for x depend on bp;
  %% the cons cases for x are identical and don't depend on bp.
  %% We could switch the order of arguments to remove the redundancy
  %% but I wanted to match the argument order of interp_pmlf_plus.
  induction(b:nat) by bp bt IHb return Forall(x:ml).{ (foldr ! ! interp_mlf_f b x) = (mult (interp_mlf x) b) } with
    Z =>
      induction(x:ml) by xp xt IHx return { (foldr ! ! interp_mlf_f b x) = (mult (interp_mlf x) b) } with
        nil A' =>
          hypjoin (foldr ! ! interp_mlf_f b x)
                  (mult (interp_mlf x) b)
               by xp bp end
      | cons A' h t =>
          abbrev hcast = cast h by symm inj <list *> xt in
          abbrev tcast = cast t by cong <list *> symm inj <list *> xt in
          hypjoin (foldr ! ! interp_mlf_f b x)
                  (mult (interp_mlf x) b)
               by xp
                  [IHx tcast]
                  [mult_assoc terminates (fst nat nat hcast) by fstTot
                              terminates (interp_mlf tcast) by interp_mlf_total
                              b] end
      end
  | S n' =>
      induction(x:ml) by xp xt IHx return { (foldr ! ! interp_mlf_f b x) = (mult (interp_mlf x) b) } with
        nil A' =>
          hypjoin (foldr ! ! interp_mlf_f b x)
                  (mult (interp_mlf x) b)
               by xp bp [plusZ n'] end
      | cons A' h t =>
          abbrev hcast = cast h by symm inj <list *> xt in
          abbrev tcast = cast t by cong <list *> symm inj <list *> xt in
          hypjoin (foldr ! ! interp_mlf_f b x)
                  (mult (interp_mlf x) b)
               by xp
                  [IHx tcast]
                  [mult_assoc terminates (fst nat nat hcast) by fstTot
                              terminates (interp_mlf tcast) by interp_mlf_total
                              b] end
      end
  end.

Define interp_pmlf_plus : Forall(b:nat)(x:pml).{ (foldr ! ! interp_pmlf_f b x) = (plus (interp_pmlf x) b) } :=
  foralli(b:nat).
    induction(x:pml) by xp xt IHx return { (foldr ! ! interp_pmlf_f b x) = (plus (interp_pmlf x) b) } with
      nil A' =>
        hypjoin (foldr ! ! interp_pmlf_f b x)
                (plus (interp_pmlf x) b)
             by xp end
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> xt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> xt in
        hypjoin (foldr ! ! interp_pmlf_f b x)
                (plus (interp_pmlf x) b)
             by xp
                [IHx tcast]
                [plus_assoc terminates (interp_mlf hcast) by interp_mlf_total
                            terminates (interp_pmlf tcast) by interp_pmlf_total
                            b] end
    end.

Define flatten_nonnil : Forall(x:pme).{ (flatten x) != (nil !) } :=
  induction(x:pme) by xp xt IHx return { (flatten x) != (nil !) } with
    nate n =>
      trans hypjoin (flatten x)
                    (cons ! (cons ! n (nil !)) (nil !))
                 by xp end
            clash (cons ! (cons ! n (nil !)) (nil !))
                  (nil !)
  | pluse e1 e2 =>
      trans hypjoin (flatten x)
                    (append ! (flatten e1) (flatten e2))
                 by xp end
            [append_nonnil ml terminates (flatten e1) by flatten_total
                              terminates (flatten e2) by flatten_total
                              [IHx e2]]
  | multe e1 e2 =>
      [ induction(ee1:pml) by ee1p ee1t IHee1 return Forall(ee1pf:{ (flatten e1) = ee1 }).{ (flatten x) != (nil !) } with
          nil A1 =>
            foralli(ee1pf:{ (flatten e1) = ee1 }).
              contra trans symm trans ee1pf ee1p
                           [IHx e1]
                { (flatten x) != (nil !) }
        | cons A1 h1 t1 =>
            foralli(ee1pf:{ (flatten e1) = ee1 }).
              [ induction(ee2:pml) by ee2p ee2t IHee2 return Forall(ee2pf:{ (flatten e2) = ee2 }).{ (flatten x) != (nil !) } with
                  nil A2 =>
                    foralli(ee2pf:{ (flatten e2) = ee2 }).
                      contra trans symm trans ee2pf ee2p
                                   [IHx e2]
                        { (flatten x) != (nil !) }
                | cons A2 h2 t2 =>
                    foralli(ee2pf:{ (flatten e2) = ee2 }).
                      trans hypjoin (flatten x)
                                    (append ! (multFT (flatten e1) h2) (multFF (flatten e1) t2))
                                 by xp
                                    trans ee1pf ee1p
                                    trans ee2pf ee2p end
                      trans cong (append ! (multFT * h2) (multFF (flatten e1) t2))
                                 trans ee1pf ee1p
                      trans join (append ! (multFT (cons ! h1 t1) h2) (multFF (flatten e1) t2))
                                 (cons ! (multTT h1 h2) (append ! (multFT t1 h2) (multFF (flatten e1) t2)))
                            clash (cons ! terminates (multTT h1 h2) by multTT_total
                                          terminates (append ! terminates (multFT t1 h2) by multFT_total
                                                               terminates (multFF terminates (flatten e1) by flatten_total t2) by multFF_total) by append_total)
                                  (nil !)
                end terminates (flatten e2) by flatten_total
                    join (flatten e2) (flatten e2) ]
        end terminates (flatten e1) by flatten_total
            join (flatten e1) (flatten e1) ]
  end.

Define interp_pmlf_f_multFT : Forall(b:nat)(x:pml)(y:ml).{ (foldr ! ! interp_pmlf_f b (multFT x y)) = (plus (mult (interp_pmlf x) (interp_mlf y)) b) } :=
  foralli(b:nat).
    induction(x:pml) by xp xt IHx return Forall(y:ml).{ (foldr ! ! interp_pmlf_f b (multFT x y)) = (plus (mult (interp_pmlf x) (interp_mlf y)) b) } with
      nil A =>
        foralli(y:ml).
          hypjoin (foldr ! ! interp_pmlf_f b (multFT x y))
                  (plus (mult (interp_pmlf x) (interp_mlf y)) b)
               by xp end
    | cons A x1 x2 =>
        foralli(y:ml).
          abbrev x1cast = cast x1 by symm inj <list *> xt in
          abbrev x2cast = cast x2 by cong <list *> symm inj <list *> xt in
          trans hypjoin (foldr ! ! interp_pmlf_f b (multFT x y))
                        (plus (mult (interp_mlf x1) (interp_mlf y)) (foldr ! ! interp_pmlf_f b (multFT x2 y)))
                     by xp
                        [append_appendf natp x1cast y]
                        [foldr_appendf natp nat interp_mlf_f (S Z) x1cast y]
                        [interp_mlf_mult terminates (interp_mlf y) by interp_mlf_total x1cast] end
          trans cong (plus (mult (interp_mlf x1) (interp_mlf y)) *)
                     [IHx x2cast y]
          trans symm [plus_assoc terminates (mult terminates (interp_mlf x1cast) by interp_mlf_total
                                                  terminates (interp_mlf y) by interp_mlf_total) by mult_total
                                 terminates (mult terminates (interp_pmlf x2cast) by interp_pmlf_total
                                                  terminates (interp_mlf y) by interp_mlf_total) by mult_total
                                 b]
          trans cong (plus * b)
                     symm [mult_distr terminates (interp_mlf x1cast) by interp_mlf_total
                                      terminates (interp_pmlf x2cast) by interp_pmlf_total
                                      terminates (interp_mlf y) by interp_mlf_total]
                hypjoin (plus (mult (plus (interp_mlf x1) (interp_pmlf x2)) (interp_mlf y)) b)
                        (plus (mult (interp_pmlf x) (interp_mlf y)) b)
                     by xp end
    end.

Define interp_pmlf_multFT : Forall(x:pml)(y:ml).{ (interp_pmlf (multFT x y)) = (mult (interp_pmlf x) (interp_mlf y)) } :=
  foralli(x:pml)(y:ml).
    trans join (interp_pmlf (multFT x y))
               (foldr ! ! interp_pmlf_f Z (multFT x y))
    trans [interp_pmlf_f_multFT Z x y]
          [plusZ terminates (mult terminates (interp_pmlf x) by interp_pmlf_total
                                  terminates (interp_mlf y) by interp_mlf_total) by mult_total].

Define interp_pmlf_multFF : Forall(x:ml)(y z:pml).{ (interp_pmlf (multFF (cons ! x y) z)) = (plus (mult (interp_mlf x) (interp_pmlf z)) (mult (interp_pmlf y) (interp_pmlf z))) } :=
  foralli(x:ml)(y:pml).
    induction(z:pml) by zp zt IHz return { (interp_pmlf (multFF (cons ! x y) z)) = (plus (mult (interp_mlf x) (interp_pmlf z)) (mult (interp_pmlf y) (interp_pmlf z))) } with
      nil A' =>
        trans hypjoin (interp_pmlf (multFF (cons ! x y) z))
                      (plus (mult (interp_mlf x) Z) (mult (interp_pmlf y) Z))
                   by zp
                      [multZ terminates (interp_mlf x) by interp_mlf_total]
                      [multZ terminates (interp_pmlf y) by interp_pmlf_total] end
              cong (plus (mult (interp_mlf x) *) (mult (interp_pmlf y) *))
                   hypjoin Z
                           (interp_pmlf z)
                        by zp end
    | cons A' z1 z2 =>
        abbrev z1cast = cast z1 by symm inj <list *> zt in
        abbrev z2cast = cast z2 by cong <list *> symm inj <list *> zt in
        trans hypjoin (interp_pmlf (multFF (cons ! x y) z))
                      (foldr ! ! interp_pmlf_f Z (append ! (multFT (cons ! x y) z1) (multFF (cons ! x y) z2)))
                   by zp end
        trans cong (foldr ! ! interp_pmlf_f Z *)
                   [append_appendf ml terminates (multFT (cons ml x y) z1cast) by multFT_total
                                      terminates (multFF (cons ml x y) z2cast) by multFF_total]
        trans [foldr_appendf ml nat interp_pmlf_f Z terminates (multFT (cons ml x y) z1cast) by multFT_total
                                                    terminates (multFF (cons ml x y) z2cast) by multFF_total]
        trans join (foldr ! ! interp_pmlf_f (foldr ! ! interp_pmlf_f Z (multFF (cons ! x y) z2)) (multFT (cons ! x y) z1cast))
                   (foldr ! ! interp_pmlf_f (interp_pmlf (multFF (cons ! x y) z2)) (multFT (cons ! x y) z1cast))
        trans cong (foldr ! ! interp_pmlf_f * (multFT (cons ! x y) z1cast))
                   [IHz z2cast]
        trans [interp_pmlf_f_multFT terminates (plus terminates (mult terminates (interp_mlf x) by interp_mlf_total
                                                                      terminates (interp_pmlf z2cast) by interp_pmlf_total) by mult_total
                                                     terminates (mult terminates (interp_pmlf y) by interp_pmlf_total
                                                                      terminates (interp_pmlf z2cast) by interp_pmlf_total) by mult_total) by plus_total
                                    (cons ml x y)
                                    z1cast]
        trans join (plus (mult (interp_pmlf (cons ! x y)) (interp_mlf z1)) (plus (mult (interp_mlf x) (interp_pmlf z2)) (mult (interp_pmlf y) (interp_pmlf z2))))
                   (plus (mult (plus (interp_mlf x) (interp_pmlf y)) (interp_mlf z1)) (plus (mult (interp_mlf x) (interp_pmlf z2)) (mult (interp_pmlf y) (interp_pmlf z2))))
        trans cong (plus * (plus (mult (interp_mlf x) (interp_pmlf z2)) (mult (interp_pmlf y) (interp_pmlf z2))))
                   [mult_distr terminates (interp_mlf x) by interp_mlf_total
                               terminates (interp_pmlf y) by interp_pmlf_total
                               terminates (interp_mlf z1cast) by interp_mlf_total]
        trans [plus_transform_1 terminates (mult terminates (interp_mlf x) by interp_mlf_total
                                                 terminates (interp_mlf z1cast) by interp_mlf_total) by mult_total
                                terminates (mult terminates (interp_mlf x) by interp_mlf_total
                                                 terminates (interp_pmlf z2cast) by interp_pmlf_total) by mult_total
                                terminates (mult terminates (interp_pmlf y) by interp_pmlf_total
                                                 terminates (interp_mlf z1cast) by interp_mlf_total) by mult_total
                                terminates (mult terminates (interp_pmlf y) by interp_pmlf_total
                                                 terminates (interp_pmlf z2cast) by interp_pmlf_total) by mult_total]
        trans symm [mult_foil terminates (interp_mlf x) by interp_mlf_total
                              terminates (interp_pmlf y) by interp_pmlf_total
                              terminates (interp_mlf z1cast) by interp_mlf_total
                              terminates (interp_pmlf z2cast) by interp_pmlf_total]
        trans symm trans join (mult (plus (interp_mlf x) (interp_pmlf y)) (interp_pmlf z))
                              (mult (plus (interp_mlf x) (interp_pmlf y)) (foldr ! ! interp_pmlf_f Z z))
                   trans cong (mult (plus (interp_mlf x) (interp_pmlf y)) (foldr ! ! interp_pmlf_f Z *)) zp
                         join (mult (plus (interp_mlf x) (interp_pmlf y)) (foldr ! ! interp_pmlf_f Z (cons ! z1 z2)))
                              (mult (plus (interp_mlf x) (interp_pmlf y)) (plus (interp_mlf z1) (interp_pmlf z2)))
              [mult_distr terminates (interp_mlf x) by interp_mlf_total
                          terminates (interp_pmlf y) by interp_pmlf_total
                          terminates (interp_pmlf z) by interp_pmlf_total]
    end.

Define flatten_equality : Forall(x:pme).{ (interp x) = (interp_pmlf (flatten x)) } :=
  induction(x:pme) by xp xt IHx return { (interp x) = (interp_pmlf (flatten x)) } with
    nate n =>
      trans hypjoin (interp x)
                    (fst ! ! n)
                 by xp end
            symm trans hypjoin (interp_pmlf (flatten x))
                               (plus (mult (fst ! ! n) (S Z)) Z)
                            by xp end
                 trans [plusZ terminates (mult terminates (fst nat nat n) by fstTot (S Z)) by mult_total]
                       [multOne terminates (fst nat nat n) by fstTot]
  | pluse e1 e2 =>
      trans hypjoin (interp x)
                    (plus (interp e1) (interp e2))
                 by xp end
            symm trans hypjoin (interp_pmlf (flatten x))
                               (foldr ! ! interp_pmlf_f (foldr ! ! interp_pmlf_f Z (flatten e2)) (flatten e1))
                            by xp
                               [append_appendf ml terminates (flatten e1) by flatten_total
                                                  terminates (flatten e2) by flatten_total]
                               [foldr_appendf ml nat interp_pmlf_f Z terminates (flatten e1) by flatten_total
                                                                     terminates (flatten e2) by flatten_total] end
                 trans cong (foldr ! ! interp_pmlf_f * (flatten e1))
                            trans join (foldr ! ! interp_pmlf_f Z (flatten e2))
                                       (interp_pmlf (flatten e2))
                                  symm [IHx e2]
                 trans [interp_pmlf_plus terminates (interp e2) by interpTot
                                         terminates (flatten e1) by flatten_total]
                       cong (plus * (interp e2))
                            symm [IHx e1]
  | multe e1 e2 =>
      [ induction(ee1:pml) by ee1p ee1t IHee1 return Forall(ee1pf:{ (flatten e1) = ee1 }).{ (interp x) = (interp_pmlf (flatten x)) } with
          nil A1 =>
            foralli(ee1pf:{ (flatten e1) = ee1 }).
              contra trans symm trans ee1pf ee1p
                           [flatten_nonnil e1]
                { (interp x) = (interp_pmlf (flatten x)) }
        | cons A1 h1 t1 =>
            foralli(ee1pf:{ (flatten e1) = ee1 }).
              [ induction(ee2:pml) by ee2p ee2t IHee2 return Forall(ee2pf:{ (flatten e2) = ee2 }).{ (interp x) = (interp_pmlf (flatten x)) } with
                  nil A2 =>
                    foralli(ee2pf:{ (flatten e2) = ee2 }).
                      contra trans symm trans ee2pf ee2p
                                   [flatten_nonnil e2]
                        { (interp x) = (interp_pmlf (flatten x)) }
                | cons A2 h2 t2 =>
                    abbrev h1cast = cast h1 by symm inj <list *> ee1t in
                    abbrev h2cast = cast h2 by symm inj <list *> ee2t in
                    abbrev t1cast = cast t1 by cong <list *> symm inj <list *> ee1t in
                    abbrev t2cast = cast t2 by cong <list *> symm inj <list *> ee2t in
                    foralli(ee2pf:{ (flatten e2) = ee2 }).
                      trans trans hypjoin (interp x)
                                          (mult (interp_pmlf (flatten e1)) (interp_pmlf (flatten e2)))
                                       by xp
                                          [IHx e1]
                                          [IHx e2] end
                            trans cong (mult (interp_pmlf *) (interp_pmlf (flatten e2)))
                                       trans ee1pf ee1p
                            trans cong (mult (interp_pmlf (cons ! h1 t1)) (interp_pmlf *))
                                       trans ee2pf ee2p
                            trans hypjoin (mult (interp_pmlf (cons ! h1 t1)) (interp_pmlf (cons ! h2 t2)))
                                          (mult (plus (interp_mlf h1) (interp_pmlf t1)) (plus (interp_mlf h2) (interp_pmlf t2)))
                                       by xp end
                                  [mult_foil terminates (interp_mlf h1cast) by interp_mlf_total
                                             terminates (interp_pmlf t1cast) by interp_pmlf_total
                                             terminates (interp_mlf h2cast) by interp_mlf_total
                                             terminates (interp_pmlf t2cast) by interp_pmlf_total]
                            symm trans hypjoin (interp_pmlf (flatten x))
                                               (plus (plus (mult (interp_mlf h1) (interp_mlf h2)) (interp_pmlf (multFT t1 h2))) (interp_pmlf (multFF (cons ! h1 t1) t2)))
                                            by xp
                                               trans ee1pf ee1p
                                               trans ee2pf ee2p
                                               [append_appendf natp h1cast h2cast]
                                               [foldr_appendf natp nat interp_mlf_f (S Z) h1cast h2cast]
                                               [interp_mlf_mult terminates (interp_mlf h2cast) by interp_mlf_total h1cast]
                                               [append_appendf ml terminates (multFT t1cast h2cast) by multFT_total
                                                                  terminates (multFF (cons ml h1cast t1cast) t2cast) by multFF_total]
                                               [foldr_appendf ml nat interp_pmlf_f Z terminates (multFT t1cast h2cast) by multFT_total
                                                                                     terminates (multFF (cons ml h1cast t1cast) t2cast) by multFF_total]
                                               [interp_pmlf_plus terminates (foldr ml nat interp_pmlf_f Z terminates (multFF (cons ml h1cast t1cast) t2cast) by multFF_total)
                                                                         by [foldrTot ml nat interp_pmlf_f interp_pmlf_f_total Z terminates (multFF (cons ml h1cast t1cast) t2cast) by multFF_total]
                                                                 terminates (multFT t1cast h2cast) by multFT_total]
                                               [plus_assoc terminates (mult terminates (interp_mlf h1cast) by interp_mlf_total
                                                                            terminates (interp_mlf h2cast) by interp_mlf_total) by mult_total
                                                           terminates (interp_pmlf terminates (multFT t1cast h2cast) by multFT_total) by interp_pmlf_total
                                                           terminates (interp_pmlf terminates (multFF (cons ml h1cast t1cast) t2cast) by multFF_total) by interp_pmlf_total] end
                                 trans cong (plus (plus (mult (interp_mlf h1) (interp_mlf h2)) *) (interp_pmlf (multFF (cons ! h1 t1) t2)))
                                            [interp_pmlf_multFT t1cast h2cast]
                                 trans cong (plus (plus (mult (interp_mlf h1) (interp_mlf h2)) (mult (interp_pmlf t1) (interp_mlf h2))) *)
                                            [interp_pmlf_multFF h1cast t1cast t2cast]
                                       [plus_transform_1 terminates (mult terminates (interp_mlf h1cast) by interp_mlf_total
                                                                          terminates (interp_mlf h2cast) by interp_mlf_total) by mult_total
                                                         terminates (mult terminates (interp_mlf h1cast) by interp_mlf_total
                                                                          terminates (interp_pmlf t2cast) by interp_pmlf_total) by mult_total
                                                         terminates (mult terminates (interp_pmlf t1cast) by interp_pmlf_total
                                                                          terminates (interp_mlf h2cast) by interp_mlf_total) by mult_total
                                                         terminates (mult terminates (interp_pmlf t1cast) by interp_pmlf_total
                                                                          terminates (interp_pmlf t2cast) by interp_pmlf_total) by mult_total]
                end terminates (flatten e2) by flatten_total
                    join (flatten e2) (flatten e2) ]
        end terminates (flatten e1) by flatten_total
            join (flatten e1) (flatten e1) ]
  end.

Set "print_parsed".

Define simplify_equality : Forall(x:pme).{ (interp x) = (interp_pmlf (simplify x)) } :=
  foralli(x:pme).
    symm trans join (interp_pmlf (simplify x))
                    (interp_pmlf (sort_pml (flatten x)))
         trans symm [sorted_interp_equiv terminates (flatten x) by flatten_total]
               symm [flatten_equality x].
