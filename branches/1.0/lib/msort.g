Include "bool.g".
Include "list.g".
Include "pair.g".
Include "plus.g".

Define split_list_length : Fun(A:type)(l:<list A>).nat :=
  fun split_list_length(A:type)(l:<list A>) : nat .
  match l by lp lt return nat with
    nil A' => Z
  | cons A' h1 t1 =>
      match t1 by t1p t1t return nat with
        nil A'' => Z
      | cons A'' h2 t2 =>
          (S (split_list_length A cast cast t2 by cong <list *> symm inj <list *> t1t by cong <list *> symm inj <list *> lt))
      end
  end.

Define split_list_helper : Fun(A:type)(l:<list A>)(n:nat).<pair <list A> <list A>> :=
  fun split_list_helper(A:type)(l:<list A>)(n:nat) : <pair <list A> <list A>> .
  match n by np nt return <pair <list A> <list A>> with
    Z =>
      (mkpair <list A> <list A> (nil A) l)
  | S n' =>
      match l by lp lt return <pair <list A> <list A>> with
        nil A' =>
            (mkpair <list A> <list A> (nil A) (nil A))
        | cons A' h t =>
            let t' = (split_list_helper A cast t by cong <list *> symm inj <list *> lt n') by s'p in
            (mkpair <list A> <list A>
                    (cons A cast h by symm inj <list *> lt (fst <list A> <list A> t'))
                    (snd <list A> <list A> t'))
      end
  end.

Define split_list : Fun(A:type)(l:<list A>).<pair <list A> <list A>> :=
  fun(A:type)(l:<list A>).
  (split_list_helper A l (split_list_length A l)).

Define split_list_length_total : Forall(A:type)(l:<list A>).Exists(n:nat).{ (split_list_length A l) = n } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Exists(n:nat).{ (split_list_length A l) = n } with
      nil A' =>
        existsi Z { (split_list_length A l) = * }
                  trans cong (split_list_length A *) lp
                        join (split_list_length A (nil A)) Z
    | cons A' h t =>
        %- Kinda silly but we need to use induction on t to split it into
           cases; we do this by assuming that the induction variable l2 is
           equal to the t in the outer context, then eliminate the
           Forall(l2) by giving it t (and the proof "join t t" which gives
           us t = l2 -- note that refl appears not to be fully implemented
           so we don't use "refl t" here). -%
        [ induction(l2:<list A>) by l2p l2t IHl2 return Forall(u:{t = l2}).Exists(n:nat).{ (split_list_length A l) = n } with
            nil A' =>
              foralli(u:{ t = l2 }).
              existsi Z { (split_list_length A l) = * }
                        trans cong (split_list_length A *) lp
                        trans cong (split_list_length A (cons A h *)) trans u l2p
                              join (split_list_length A (cons A h (nil A))) Z
          | cons A' h2 t2 =>
              foralli(u:{ t = l2 }).
              existse [IHl cast t2 by cong <list *> symm inj <list *> l2t]
                foralli(n:nat)(u2:{ (split_list_length A t2) = n }).
                  existsi (S n) { (split_list_length A l) = * }
                    trans cong (split_list_length A *) lp
                    trans cong (split_list_length A (cons A h *)) trans u l2p
                    trans join (split_list_length A (cons A h (cons A h2 t2)))
                               (S (split_list_length A t2))
                          cong (S *) u2
          end cast t by cong <list *> symm inj <list *> lt join t t]
    end.

Define split_list_helper_total : Forall(A:type)(l:<list A>)(n:nat).Exists(o:<pair <list A> <list A>>).{ (split_list_helper A l n) = o } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(n:nat).Exists(o:<pair <list A> <list A>>).{ (split_list_helper A l n) = o } with
      nil A' =>
        induction(n:nat) by np nt IHn return Exists(o:<pair <list A> <list A>>).{ (split_list_helper A l n) = o } with
          Z =>
            existsi (mkpair <list A> <list A> (nil A) l)
                    { (split_list_helper A l n) = * }
                    trans cong (split_list_helper A l *) np
                          join (split_list_helper A l Z)
                               (mkpair <list A> <list A> (nil A) l)
          | S n' =>
            existsi (mkpair <list A> <list A> (nil A) (nil A))
                    { (split_list_helper A l n) = * }
                    trans cong (split_list_helper A * n) lp
                    trans cong (split_list_helper A (nil A) *) np
                          join (split_list_helper A (nil A) (S n'))
                               (mkpair <list A> <list A> (nil A) (nil A))
          end
    | cons A' h t =>
        induction(n:nat) by np nt IHn return Exists(o:<pair <list A> <list A>>).{ (split_list_helper A l n) = o } with
          Z =>
            existsi (mkpair <list A> <list A> (nil A) l)
                    { (split_list_helper A l n) = * }
                    trans cong (split_list_helper A l *) np
                          join (split_list_helper A l Z)
                               (mkpair <list A> <list A> (nil A) l)
          | S n' =>
            abbrev t' = (split_list_helper A cast t by cong <list *> symm inj <list *> lt n') in
            existsi (mkpair <list A> <list A> (cons A cast h by symm inj <list *> lt terminates (fst <list A> <list A> t') by fstTot) terminates (snd <list A> <list A> t') by sndTot)
                    { (split_list_helper A l n) = * }
                    trans cong (split_list_helper A * n) lp
                    trans cong (split_list_helper A (cons A h t) *) np
                          join (split_list_helper A (cons A h t) (S n'))
                               (mkpair <list A> <list A> (cons A h (fst <list A> <list A> t')) (snd <list A> <list A> t'))
          end
    end.

Define split_list_total : Forall(A:type)(l:<list A>).Exists(o:<pair <list A> <list A>>).{ (split_list A l) = o } :=
  foralli(A:type)(l:<list A>).
    existse [split_list_length_total A l]
      foralli(n:nat)(u:{ (split_list_length A l) = n }).
        existse [split_list_helper_total A l n]
          foralli(o:<pair <list A> <list A>>)(u2:{ (split_list_helper A l n) = o }).
            existsi o { (split_list A l) = * }
              trans join (split_list A l)
                         (split_list_helper A l (split_list_length A l))
              trans cong (split_list_helper A l *) u
                    u2.

Define append_split_list_helper : Forall(A:type)(l:<list A>)(n:nat).{ (append A (fst <list A> <list A> (split_list_helper A l n)) (snd <list A> <list A> (split_list_helper A l n))) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(n:nat).{ (append A (fst <list A> <list A> (split_list_helper A l n)) (snd <list A> <list A> (split_list_helper A l n))) = l } with
      nil A' =>
        induction(n:nat) by np nt IHn return { (append A (fst <list A> <list A> (split_list_helper A l n)) (snd <list A> <list A> (split_list_helper A l n))) = l } with
          Z =>
            abbrev sol = (mkpair <list A> <list A> (nil A) (nil A)) in
            symm trans lp
                 trans join (nil A) (append A (nil A) (nil A))
                 trans cong (append A * (nil A))
                            join (nil A) (fst <list A> <list A> sol)
                 trans cong (append A (fst <list A> <list A> sol) *)
                            join (nil A) (snd <list A> <list A> sol)
                       cong (append A (fst <list A> <list A> *) (snd <list A> <list A> *))
                            trans join sol
                                       (split_list_helper A (nil A) Z)
                            trans cong (split_list_helper A * Z) symm lp
                                  cong (split_list_helper A l *) symm np
        | S n' =>
            abbrev sol = (mkpair <list A> <list A> (nil A) (nil A)) in
            symm trans lp
                 trans join (nil A) (append A (nil A) (nil A))
                 trans cong (append A * (nil A))
                            join (nil A) (fst <list A> <list A> sol)
                 trans cong (append A (fst <list A> <list A> sol) *)
                            join (nil A) (snd <list A> <list A> sol)
                       cong (append A (fst <list A> <list A> *) (snd <list A> <list A> *))
                            trans join sol
                                       (split_list_helper A (nil A) (S n'))
                            trans cong (split_list_helper A * (S n')) symm lp
                                  cong (split_list_helper A l *) symm np
        end
    | cons A' h t =>
        induction(n:nat) by np nt IHn return { (append A (fst <list A> <list A> (split_list_helper A l n)) (snd <list A> <list A> (split_list_helper A l n))) = l } with
          Z =>
            trans cong (append A (fst <list A> <list A> *) (snd <list A> <list A> *))
                       trans cong (split_list_helper A l *) np
                             join (split_list_helper A l Z)
                                  (mkpair <list A> <list A> (nil A) l)
            trans cong (append A * (snd <list A> <list A> (mkpair <list A> <list A> (nil A) l)))
                       join (fst <list A> <list A> (mkpair <list A> <list A> (nil A) l)) (nil A)
            trans cong (append A (nil A) *)
                       join (snd <list A> <list A> (mkpair <list A> <list A> (nil A) l)) l
                  join (append A (nil A) l) l
        | S n' =>
            trans cong (append A (fst <list A> <list A> (split_list_helper A l *)) (snd <list A> <list A> (split_list_helper A l *)))
                       np
            trans cong (append A (fst <list A> <list A> *) (snd <list A> <list A> *))
                       trans cong (split_list_helper A * (S n')) lp
                             join (split_list_helper A (cons A h t) (S n'))
                                  (mkpair <list A> <list A>
                                          (cons A h (fst <list A> <list A> (split_list_helper A t n')))
                                          (snd <list A> <list A> (split_list_helper A t n')))
            trans cong (append A * (snd <list A> <list A> (mkpair <list A> <list A> (cons A h (fst <list A> <list A> (split_list_helper A t n'))) (snd <list A> <list A> (split_list_helper A t n')))))
                       join (fst <list A> <list A> (mkpair <list A> <list A> (cons A h (fst <list A> <list A> (split_list_helper A t n'))) (snd <list A> <list A> (split_list_helper A t n'))))
                            (cons A h (fst <list A> <list A> (split_list_helper A t n')))
            trans cong (append A (cons A h (fst <list A> <list A> (split_list_helper A t n'))) *)
                       join (snd <list A> <list A> (mkpair <list A> <list A> (cons A h (fst <list A> <list A> (split_list_helper A t n'))) (snd <list A> <list A> (split_list_helper A t n'))))
                            (snd <list A> <list A> (split_list_helper A t n'))
            trans join (append A (cons A h (fst <list A> <list A> (split_list_helper A t n'))) (snd <list A> <list A> (split_list_helper A t n')))
                       (cons A h (append A (fst <list A> <list A> (split_list_helper A t n')) (snd <list A> <list A> (split_list_helper A t n'))))
            trans cong (cons A h *)
                       [IHl cast t by cong <list *> symm inj <list *> lt n']
                  symm lp
        end
    end.

% : Forall(A:type)(l:<list A>)(n:nat).{ (append A (fst <list A> <list A> (split_list_helper A l n)) (snd <list A> <list A> (split_list_helper A l n))) = l } :=

Define append_split_list : Forall(A:type)(l:<list A>).{ (append A (fst <list A> <list A> (split_list A l)) (snd <list A> <list A> (split_list A l))) = l } :=
  foralli(A:type)(l:<list A>).
    symm trans existse [split_list_length_total A l]
                       foralli(n:nat)(u:{ (split_list_length A l) = n }).
                         trans symm [append_split_list_helper A l n]
                               cong (append A (fst <list A> <list A> (split_list_helper A l *)) (snd <list A> <list A> (split_list_helper A l *))) symm u
               cong (append A (fst <list A> <list A> *) (snd <list A> <list A> *))
                    join (split_list_helper A l (split_list_length A l))
                         (split_list A l).

Define merge : Fun(A:type)(x y : <list A>)(cmp:Fun(x y : A).bool).<list A> :=
	fun merge(A:type)(x y : <list A>)(cmp:Fun(x y : A).bool) : <list A>.
	match x by ux vx return <list A> with
		nil A' => y
		| cons A' ax' lx' =>
			match y by uy vy return <list A> with
				nil A' => x
				| cons A' ay' ly' =>
					abbrev p = symm inj <list *> vx in
					abbrev q = symm inj <list *> vy in
					match (cmp cast ax' by p  cast ay' by q) by u v return <list A> with
						  ff => (cons A cast ax' by p (merge A cast lx' by cong <list *> p y cmp))
						| tt => (cons A cast ay' by q (merge A x cast ly' by cong <list *> q cmp))
					end
			end
	end.

Define msort : Fun(A:type)(l:<list A>)(cmp:Fun(x y : A).bool).<list A> :=
	fun msort(A:type)(l:<list A>)(cmp:Fun(x y : A).bool) : <list A>.
	match l by u v return <list A> with
	  nil A' => l
	| cons A' a' l' =>
		abbrev p = symm inj <list *> v in
		match l' by l'p l't return <list A> with
			  nil A' => (cons A cast a' by p (nil A))
			| cons A'' a'' l'' =>
				let q = (split_list A l) by xyz in
				(merge A (msort A (fst <list A> <list A> q) cmp) (msort A (snd <list A> <list A> q) cmp) cmp)
		end
	end.

Define merge_total : Forall(A:type)(x y:<list A>)(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).Exists(o:<list A>).{ (merge A x y cmp) = o } :=
  foralli(A:type).
    induction(x:<list A>) by xp xt IHx return Forall(y:<list A>)(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).Exists(o:<list A>).{ (merge A x y cmp) = o } with
      nil A' =>
        foralli(y:<list A>)(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          existsi y { (merge A x y cmp) = * }
            trans cong (merge A * y cmp) xp
                  join (merge A (nil A) y cmp) y
    | cons A' ax' lx' =>
        induction(y:<list A>) by yp yt IHy return Forall(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).Exists(o:<list A>).{ (merge A x y cmp) = o } with
          nil A'' =>
            foralli(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              existsi x { (merge A x y cmp) = * }
                trans cong (merge A * y cmp) xp
                trans cong (merge A (cons A' ax' lx') * cmp) yp
                trans join (merge A (cons A' ax' lx') (nil A) cmp) (cons A' ax' lx')
                      symm xp
        | cons A'' ay' ly' =>
            foralli(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              existse [cmp_total cast ax' by symm inj <list *> xt cast ay' by symm inj <list *> yt]
                      induction(b:bool) by bp bt IHb return Forall(u:{ (cmp ax' ay') = b }).Exists(o:<list A>).{ (merge A x y cmp) = o } with
                        ff =>
                          foralli(u:{ (cmp ax' ay') = b }).
                            existsi (cons A cast ax' by symm inj <list *> xt
                                            terminates (merge A cast lx' by cong <list *> symm inj <list *> xt y cmp)
                                                    by [IHx cast lx' by cong <list *> symm inj <list *> xt y cmp cmp_total])
                                    { (merge A x y cmp) = * }
                              trans cong (merge A * y cmp) xp
                              trans cong (merge A (cons A' ax' lx') * cmp) yp
                              trans join (merge A (cons A' ax' lx') (cons A'' ay' ly') cmp)
                                         match (cmp ax' ay') by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                              trans cong match * by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                                         trans u bp
                              trans join match ff by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                                         (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                    cong (cons A ax' (merge A lx' * cmp))
                                         symm yp
                      | tt =>
                          foralli(u:{ (cmp ax' ay') = b }).
                            existsi (cons A cast ay' by symm inj <list *> yt
                                            terminates (merge A x cast ly' by cong <list *> symm inj <list *> yt cmp)
                                                    by [IHy cast ly' by cong <list *> symm inj <list *> yt cmp cmp_total])
                                    { (merge A x y cmp) = * }
                              trans cong (merge A * y cmp) xp
                              trans cong (merge A (cons A' ax' lx') * cmp) yp
                              trans join (merge A (cons A' ax' lx') (cons A'' ay' ly') cmp)
                                         match (cmp ax' ay') by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                              trans cong match * by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                                         trans u bp
                              trans join match tt by u v return <list A> with
                                           ff => (cons A ax' (merge A lx' (cons A ay' ly') cmp))
                                         | tt => (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                         end
                                         (cons A ay' (merge A (cons A ax' lx') ly' cmp))
                                    cong (cons A ay' (merge A * ly' cmp))
                                         symm xp
                      end
        end
    end.

Define split_list_len_fst_len : Forall(A:type)
                                      (l:<list A>)
                                      (n:nat)
                                      (u:{ (lt (list_length A l) n) = tt }).
                                   { (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) } :=
  foralli(A:type).
    induction(l:<list A>) by lp ltyp IHl return Forall(n:nat)(u:{ (lt (list_length A l) n) = tt }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) } with
      nil A' =>
        induction(n:nat) by np ntyp IHn return Forall(u:{ (lt (list_length A l) n) = tt }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) } with
          Z =>
            foralli(u:{ (lt (list_length A l) n) = tt }).
              contra trans symm u
                     trans cong (lt (list_length ! *) n) lp
                     trans cong (lt * n)
                                join (list_length ! (nil !)) Z
                     trans cong (lt Z *)
                                np
                     trans join (lt Z Z) ff
                           clash ff tt
                { (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) }
        | S n' =>
            foralli(u:{ (lt (list_length A l) n) = tt }).
              trans cong (list_length ! (fst ! ! (split_list_helper ! * n))) lp
              trans cong (list_length ! (fst ! ! (split_list_helper ! (nil !) *))) np
              trans cong (list_length ! (fst ! ! *))
                         join (split_list_helper ! (nil !) (S n')) (mkpair ! ! (nil !) (nil !))
                    cong (list_length ! *)
                         trans join (fst ! ! (mkpair ! ! (nil !) (nil !))) (nil !)
                               symm lp
        end
    | cons A' h t =>
        induction(n:nat) by np ntyp IHn return Forall(u:{ (lt (list_length A l) n) = tt }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) } with
          Z =>
            foralli(u:{ (lt (list_length A l) n) = tt }).
              contra trans symm u
                     trans cong (lt (list_length ! *) n) lp
                     trans cong (lt * n)
                                join (list_length ! (cons ! h t)) (S (list_length ! t))
                     trans cong (lt (S (list_length ! t)) *)
                                np
                     trans join (lt (S (list_length ! t)) Z) ff
                           clash ff tt
                { (list_length A (fst <list A> <list A> (split_list_helper A l n))) = (list_length A l) }
        | S n' =>
            foralli(u:{ (lt (list_length A l) n) = tt }).
              abbrev u' = trans join (lt (list_length ! t) n')
                                     (lt (S (list_length ! t)) (S n'))
                          trans cong (lt (S (list_length ! t)) *)
                                     symm np
                          trans cong (lt * n)
                                     trans join (S (list_length ! t))
                                                (list_length ! (cons ! h t))
                                           cong (list_length ! *) symm lp
                                u in
              trans cong (list_length ! (fst ! ! (split_list_helper ! * n))) lp
              trans cong (list_length ! (fst ! ! (split_list_helper ! (cons ! h t) *))) np
              trans join (list_length ! (fst ! ! (split_list_helper ! (cons ! h t) (S n'))))
                         (S (list_length ! (fst ! ! (split_list_helper ! t n'))))
              trans cong (S *)
                         [IHl cast t by cong <list *> symm inj <list *> ltyp n' u']
              trans join (S (list_length ! t))
                         (list_length ! (cons ! h t))
                    cong (list_length ! *)
                         symm lp
        end
    end.

Define split_list_len_fst_n : Forall(A:type)
                                    (l:<list A>)
                                    (n:nat)
                                    (u:{ (lt (list_length A l) n) = ff }).
                                 { (list_length A (fst <list A> <list A> (split_list_helper A l n))) = n } :=
  foralli(A:type).
    induction(l:<list A>) by lp ltyp IHl return Forall(n:nat)(u:{ (lt (list_length A l) n) = ff }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = n } with
      nil A' =>
        induction(n:nat) by np ntyp IHn return Forall(u:{ (lt (list_length A l) n) = ff }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = n } with
          Z =>
            foralli(u:{ (lt (list_length A l) n) = ff }).
              trans cong (list_length ! (fst ! ! (split_list_helper ! l *))) np
              trans cong (list_length ! (fst ! ! *))
                         join (split_list_helper ! l Z) (mkpair ! ! (nil !) l)
              trans cong (list_length ! *)
                         join (fst ! ! (mkpair ! ! (nil !) l)) (nil !)
              trans join (list_length ! (nil !)) Z
                    symm np
        | S n' =>
            foralli(u:{ (lt (list_length A l) n) = ff }).
              contra trans symm u
                     trans cong (lt (list_length ! *) n) lp
                     trans cong (lt * n)
                                join (list_length ! (nil !)) Z
                     trans cong (lt Z *)
                                np
                     trans join (lt Z (S n')) tt
                           clash tt ff
                { (list_length A (fst <list A> <list A> (split_list_helper A l n))) = n }
        end
    | cons A' h t =>
        induction(n:nat) by np ntyp IHn return Forall(u:{ (lt (list_length A l) n) = ff }).{ (list_length A (fst <list A> <list A> (split_list_helper A l n))) = n } with
          Z =>
            foralli(u:{ (lt (list_length A l) n) = ff }).
              trans cong (list_length ! (fst ! ! (split_list_helper ! l *))) np
              trans cong (list_length ! (fst ! ! *))
                         join (split_list_helper ! l Z) (mkpair ! ! (nil !) l)
              trans cong (list_length ! *)
                         join (fst ! ! (mkpair ! ! (nil !) l)) (nil !)
              trans join (list_length ! (nil !)) Z
                    symm np
        | S n' =>
            foralli(u:{ (lt (list_length A l) n) = ff }).
              abbrev u' = trans join (lt (list_length ! t) n')
                                     (lt (S (list_length ! t)) (S n'))
                          trans cong (lt (S (list_length ! t)) *)
                                     symm np
                          trans cong (lt * n)
                                     trans join (S (list_length ! t))
                                                (list_length ! (cons ! h t))
                                           cong (list_length ! *) symm lp
                                u in
              trans cong (list_length ! (fst ! ! (split_list_helper ! * n))) lp
              trans cong (list_length ! (fst ! ! (split_list_helper ! (cons ! h t) *))) np
              trans join (list_length ! (fst ! ! (split_list_helper ! (cons ! h t) (S n'))))
                         (S (list_length ! (fst ! ! (split_list_helper ! t n'))))
              trans cong (S *)
                         [IHl cast t by cong <list *> symm inj <list *> ltyp n' u']
                    symm np
        end
    end.

Define split_list_len_fst_le_n : Forall(A:type)
                                       (l:<list A>)
                                       (n:nat).
                                    { (lt n (list_length A (fst <list A> <list A> (split_list_helper A l n)))) = ff } :=
  foralli(A:type)(l:<list A>)(n:nat).
    existse [split_list_helper_total A l n]
      foralli(o:<pair <list A> <list A>>)(u:{ (split_list_helper A l n) = o }).
        existse [fstTot <list A> <list A> o]
          foralli(z:<list A>)(u2:{ (fst <list A> <list A> o) = z }).
            existse [list_length_total A z]
              foralli(n2:nat)(u3:{ (list_length A z) = n2 }).
                abbrev congs = trans cong (lt n (list_length ! (fst ! ! *))) u
                               trans cong (lt n (list_length ! *)) u2
                                     cong (lt n *) u3 in
                existse [lt_total n n2]
                  foralli(q:bool)(u4:{ (lt n n2) = q }).
                    [ induction(qq:bool) by qqp qqt IHqq return Forall(qqq:{ q = qq }).{ (lt n (list_length A (fst <list A> <list A> (split_list_helper A l n)))) = ff } with
                        ff =>
                          foralli(qqq:{ q = qq }).
                            trans congs
                            trans u4
                            trans qqq qqp
                      | tt =>
                          foralli(qqq:{ q = qq }).
                            existse [list_length_total A l]
                              foralli(n3:nat)(u5:{ (list_length A l) = n3 }).
                                existse [lt_total n3 n]
                                  induction(q2:bool) by q2p q2t IHq2 return Forall(u6:{ (lt n3 n) = q2 }).{ (lt n (list_length A (fst <list A> <list A> (split_list_helper A l n)))) = ff } with
                                    ff =>
                                      foralli(u6:{ (lt n3 n) = q2 }).
                                        abbrev ltff = trans cong (lt * n) u5
                                                      trans u6 q2p in
                                        trans cong (lt n *) [split_list_len_fst_n A l n ltff]
                                              [x_lt_x n]
                                  | tt =>
                                      foralli(u6:{ (lt n3 n) = q2 }).
                                        abbrev lttt = trans cong (lt * n) u5
                                                      trans u6 q2p in
                                        abbrev n_lt_n2 = trans u4
                                                         trans qqq
                                                               qqp in
                                        abbrev n3_lt_n = trans u6 q2p in
                                        abbrev n2_eq_n3 = trans symm u3
                                                          trans cong (list_length ! *)
                                                                     symm u2
                                                          trans cong (list_length ! (fst ! ! *))
                                                                     symm u
                                                          trans [split_list_len_fst_len A l n lttt]
                                                                u5 in
                                        abbrev n_lt_n3 = trans cong (lt n *) symm n2_eq_n3
                                                               n_lt_n2 in
                                        contra trans symm [lt_trans n n3 n n_lt_n3 n3_lt_n]
                                               trans [x_lt_x n]
                                                     clash ff tt
                                          { (lt n (list_length A (fst <list A> <list A> (split_list_helper A l n)))) = ff }
                                  end
                      end q join q q ].

Define split_len_lt_len : Forall(A:type)
                                (l:<list A>)
                                (u:{ l != (nil A) }).
                             { (lt (split_list_length A l) (list_length A l)) = tt } :=
  foralli(A:type).
    induction(l:<list A>) by lp ltyp IHl return Forall(u:{ l != (nil A) }).{ (lt (split_list_length A l) (list_length A l)) = tt } with
      nil A' =>
        foralli(u:{ l != (nil A) }).
          contra trans lp symm u
            { (lt (split_list_length A l) (list_length A l)) = tt }
    | cons A' h t =>
        foralli(u:{ l != (nil A) }).
          abbrev tcast = cast t by cong <list *> symm inj <list *> ltyp in
          [ induction(t1:<list A>) by t1p t1t IHt1 return Forall(tt1:{ t = t1 }).{ (lt (split_list_length A l) (list_length A l)) = tt } with
              nil A'' =>
                foralli(tt1:{ t = t1 }).
                  trans cong (lt * (list_length ! l))
                             trans cong (split_list_length ! *) lp
                             trans cong (split_list_length ! (cons ! h *)) trans tt1 t1p
                                   join (split_list_length ! (cons ! h (nil !))) Z
                  trans cong (lt Z *)
                             trans cong (list_length ! *) lp
                             trans cong (list_length ! (cons ! h *)) trans tt1 t1p
                                   join (list_length ! (cons ! h (nil !))) (S Z)
                        join (lt Z (S Z)) tt
            | cons A'' h' t' =>
                foralli(tt1:{ t = t1 }).
                  abbrev t'cast = cast t' by cong <list *> symm inj <list *> t1t in
                  existse [split_list_length_total A t'cast]
                    foralli(n:nat)(u:{ (split_list_length A t') = n }).
                      [ induction(t2:<list A>) by t2p t2t IHt2 return Forall(tt2:{ t' = t2 }).{ (lt (split_list_length A l) (list_length A l)) = tt } with
                          nil A''' =>
                            foralli(tt2:{ t' = t2 }).
                              trans cong (lt (split_list_length ! *) (list_length ! *)) lp
                              trans cong (lt (split_list_length ! (cons ! h *)) (list_length ! (cons ! h *))) trans tt1 t1p
                              trans cong (lt (split_list_length ! (cons ! h (cons ! h' *))) (list_length ! (cons ! h (cons ! h' *)))) trans tt2 t2p
                              trans cong (lt * (list_length ! (cons ! h (cons ! h' (nil !)))))
                                         join (split_list_length ! (cons ! h (cons ! h' (nil !)))) (S Z)
                              trans cong (lt (S Z) *)
                                         join (list_length ! (cons ! h (cons ! h' (nil !)))) (S (S Z))
                                    join (lt (S Z) (S (S Z))) tt
                        | cons A''' h'' t'' =>
                            foralli(tt2:{ t' = t2 }).
                              existse [list_length_total A t'cast]
                                foralli(ll:nat)(llu:{ (list_length A t') = ll }).
                                  abbrev Sn_lt_SSn = [lt_S (S n)] in
                                  abbrev t'nonnil = trans tt2 trans t2p clash (cons ! h'' t'') (nil !) in
                                  abbrev n_lt_ll = symm trans symm [IHl t'cast t'nonnil]
                                                        trans cong (lt * (list_length ! t')) u
                                                              cong (lt n *) llu in
                                  abbrev Sn_lt_Sll = trans [S_lt_S n ll] n_lt_ll in
                                  abbrev Sll_lt_SSll = [lt_S (S ll)] in
                                  abbrev Sn_eq_sll = trans cong (S *) symm u
                                                     trans join (S (split_list_length ! t'))
                                                                (split_list_length ! (cons ! h (cons ! h' t')))
                                                     trans cong (split_list_length ! (cons ! h *)) symm trans tt1 t1p
                                                           cong (split_list_length ! *) symm lp in
                                  abbrev SSll_eq_llen = trans join (S (S (list_length ! t')))
                                                                   (list_length ! (cons ! h (cons ! h' t')))
                                                        trans cong (list_length ! (cons ! h *)) symm trans tt1 t1p
                                                              cong (list_length ! *) symm lp in
                                  % now we have:   split_list_length l = S n < S ll < S S ll = list_length l
                                  abbrev sll_lt_Sll = trans cong (lt * (S ll))
                                                                 trans cong (split_list_length ! (cons ! h *)) symm trans tt1 t1p
                                                                 trans cong (split_list_length ! *) symm lp
                                                                       symm Sn_eq_sll
                                                            Sn_lt_Sll in
                                  abbrev sll_lt_SSll = [lt_trans terminates (split_list_length A (cons A cast h by symm inj <list *> ltyp
                                                                                                         (cons A cast h' by symm inj <list *> t1t
                                                                                                                 cast t' by cong <list *> symm inj <list *> t1t)))
                                                                            by split_list_length_total (S ll) (S (S ll)) sll_lt_Sll Sll_lt_SSll] in
                                  symm trans symm sll_lt_SSll% stupid trick, get rid of the "= tt" for now
                                       trans cong (lt (split_list_length ! (cons ! h (cons ! h' t'))) (S (S *))) symm llu
                                       trans cong (lt (split_list_length ! (cons ! h (cons ! h' t'))) *) SSll_eq_llen
                                       trans cong (lt (split_list_length ! (cons ! h *)) (list_length ! l)) symm trans tt1 t1p
                                             cong (lt (split_list_length ! *) (list_length ! l)) symm lp
                        end t'cast join t'cast t'cast ]
            end tcast join tcast tcast ]
    end.

Define fst_len_split_list_len : Forall(A:type)
                                      (l:<list A>).
                                 { (list_length ! (fst ! ! (split_list ! l))) = (split_list_length ! l) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (list_length ! (fst ! ! (split_list ! l))) = (split_list_length ! l) } with
      nil A' =>
        trans cong (list_length ! (fst ! ! (split_list ! *))) lp
        trans join (list_length ! (fst ! ! (split_list ! (nil !))))
                   (split_list_length ! (nil !))
              cong (split_list_length ! *) symm lp
    | cons A' h t =>
        abbrev l_nonnil = trans lp clash (cons ! h t) (nil !) in
        abbrev len = terminates (list_length A l) by list_length_total in
        abbrev n = terminates (split_list_length A l) by split_list_length_total in
        abbrev len_l_ltff_splitlen_l = [lt_ltff n len
                                                [split_len_lt_len A l l_nonnil]] in
        symm trans symm [split_list_len_fst_n A l n len_l_ltff_splitlen_l]
                   cong (list_length ! (fst ! ! *))
                        join (split_list_helper ! l n)
                             (split_list ! l)
    end.

Define split_len_le_len : Forall(A:type)
                                (l:<list A>).
                             { (le (split_list_length ! l) (list_length ! l)) = tt } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (le (split_list_length A l) (list_length A l)) = tt } with
      nil A' =>
        symm trans symm [x_le_x terminates (split_list_length A l) by split_list_length_total]
                   cong (le (split_list_length ! l) *)
                        trans cong (split_list_length ! *) lp
                        trans join (split_list_length ! (nil !))
                                   (list_length ! (nil !))
                              cong (list_length ! *) symm lp
    | cons A' h t =>
        abbrev u = trans lp clash (cons ! h t) (nil !) in
        [lt_implies_le terminates (split_list_length A l) by split_list_length_total
                       terminates (list_length A l) by list_length_total
                       [split_len_lt_len A l u]]
    end.

Define split_list_lt_fst : Forall(A:type)
                                 (l:<list A>)
                                 (u:{ l != (nil !) }).
                             { (lt (list_length ! (fst ! ! (split_list ! l))) (list_length ! l)) = tt } :=
  foralli(A:type)(l:<list A>)(u:{ l != (nil A) }).
    abbrev ll = terminates (list_length A l) by list_length_total in
    abbrev sll = terminates (split_list_length A l) by split_list_length_total in
    abbrev ll_fst_slh_sll = terminates (list_length A
                                        terminates (fst <list A> <list A>
                                                    terminates (split_list_helper A l
                                                                terminates (split_list_length A l) by split_list_length_total)
                                                    by split_list_helper_total)
                                        by fstTot)
                            by list_length_total in
    abbrev sll_lt_ll = [split_len_lt_len A l u] in
    abbrev lt_sll_ll_fst_sl_eq_lt_sll_ll_fst_slh_sll = join (split_list A l)
                                                            (split_list_helper A l (split_list_length A l)) in
    abbrev ll_fst_slh_sll_le_sll = [lt_ff_implies_le sll
                                                     ll_fst_slh_sll
                                                     [split_list_len_fst_le_n A l
                                                      terminates (split_list_length A l) by split_list_length_total]] in
    symm trans symm [lelt_trans ll_fst_slh_sll sll ll ll_fst_slh_sll_le_sll sll_lt_ll]
               cong (lt (list_length ! (fst ! ! *)) ll)
                    symm lt_sll_ll_fst_sl_eq_lt_sll_ll_fst_slh_sll.

Define split_list_le_fst : Forall(A:type)
                                 (l:<list A>).
                             { (le (list_length ! (fst ! ! (split_list ! l))) (list_length ! l)) = tt } :=
  foralli(A:type).
    induction(l:<list A>) by lp _lt IHl return { (le (list_length ! (fst ! ! (split_list ! l))) (list_length ! l)) = tt } with
      nil A' =>
        symm trans symm [x_le_x terminates (list_length A l) by list_length_total]
                   cong (le * (list_length ! l))
                        symm trans cong (list_length ! (fst ! ! (split_list ! *))) lp
                             trans join (list_length ! (fst ! ! (split_list ! (nil !))))
                                        (list_length ! (nil !))
                                   cong (list_length ! *) symm lp

    | cons A' h t =>
        [lt_implies_le terminates (list_length A terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot) by list_length_total
                       terminates (list_length A l) by list_length_total
                       [split_list_lt_fst A l trans lp clash (cons ! h t) (nil !)]]
    end.

Define split_list_le_snd : Forall(A:type)
                                 (l:<list A>).
                             { (le (list_length ! (snd ! ! (split_list ! l))) (list_length ! l)) = tt } :=
  foralli(A:type)(l:<list A>).
    abbrev l1 = terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot in
    abbrev l2 = terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot in

    % (append ! l1 l2) = l
    abbrev append_l1_l2_is_l = [append_split_list A l] in

    % (list_length ! (fst ! ! (split_list ! l))) = (split_list_length ! l)
    abbrev ll_fst_l = symm trans symm [split_list_len_fst_n A l
                                                            terminates (split_list_length A l) by split_list_length_total
                                                            [le_tt_implies_lt_ff terminates (split_list_length A l) by split_list_length_total
                                                                                 terminates (list_length A l) by list_length_total
                                                                                 [split_len_le_len A l]]]
                                 cong (list_length ! (fst ! ! *))
                                      join (split_list_helper ! l (split_list_length ! l))
                                           (split_list ! l) in

    % (list_length ! l2) = (minus (list_length ! l) (split_list_length ! l))
    abbrev l2len_is_ll_minus_sll = trans symm [append_sublength_l2 A l1 l2]
                                   trans cong (minus (list_length ! *) (list_length ! l1)) append_l1_l2_is_l
                                         cong (minus (list_length ! l) *) ll_fst_l in

    [minus_le terminates (list_length A l) by list_length_total
              terminates (split_list_length A l) by split_list_length_total
              terminates (list_length A l2) by list_length_total
              symm l2len_is_ll_minus_sll].

Define split_list_nonnil_fst : Forall(A:type)
                                     (l:<list A>)
                                     (lne:{ l != (nil !) })
                                     (lnne:Forall(x:A).{ l != (cons ! x (nil !)) }).
                                 { (fst ! ! (split_list ! l)) != (nil !) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) })
                                                    (lnne:Forall(x:A).{ l != (cons ! x (nil !)) }).
                                                { (fst ! ! (split_list ! l)) != (nil !) } with
      nil A' =>
        foralli(lne:{ l != (nil !) })
               (lnne:Forall(x:A).{ l != (cons ! x (nil !)) }).
          contra trans symm lp lne
            { (fst ! ! (split_list ! l)) != (nil !) }
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(lne:{ l != (nil !) })
               (lnne:Forall(x:A).{ l != (cons ! x (nil !)) }).
          [ induction(sll:nat) by sllp sllt IHsll return Forall(sllpf:{ (split_list_length ! l) = sll }).{ (fst ! ! (split_list ! l)) != (nil !) } with
              Z =>
               foralli(sllpf:{ (split_list_length ! l) = sll }).
                 abbrev sllZ = trans sllpf sllp in
                 [ induction(t2:<list A>) by t2p t2t IHt2 return Forall(t2pf:{ t = t2 }).{ (fst ! ! (split_list ! l)) != (nil !) } with
                     nil A'' =>
                       foralli(t2pf:{ t = t2 }).
                         abbrev lcn = trans lp cong (cons ! h *) trans t2pf t2p in % l = cons h nil
                         contra trans symm lcn [lnne hcast]
                           { (fst ! ! (split_list ! l)) != (nil !) }
                   | cons A'' h' t' =>
                       abbrev h'cast = cast h' by symm inj <list *> t2t in
                       abbrev t'cast = cast t' by cong <list *> symm inj <list *> t2t in
                       foralli(t2pf:{ t = t2 }).
                         abbrev lcc = trans lp cong (cons ! h *) trans t2pf t2p in % l = cons h cons h' t'
                         existse [fstTot <list A> <list A>
                                  terminates (split_list_helper A (cons A h'cast t'cast)
                                                                terminates (split_list_length A t'cast) by split_list_length_total) by split_list_helper_total]
                           foralli(fsts:<list A>)(fstspf:{ (fst ! ! (split_list_helper ! (cons ! h' t') (split_list_length ! t'))) = fsts }).
                             trans cong (fst ! ! (split_list ! *)) lcc
                             trans join (fst ! ! (split_list ! (cons ! h (cons ! h' t'))))
                                        (cons ! h (fst ! ! (split_list_helper ! (cons ! h' t') (split_list_length ! t'))))
                             trans cong (cons ! h *)
                                        fstspf
                                   clash (cons ! h fsts)
                                         (nil !)
                   end tcast join t t ]
            | S sll' =>
               foralli(sllpf:{ (split_list_length ! l) = sll }).
                 abbrev sllS = trans sllpf sllp in
                 existse [fstTot <list A> <list A>
                          terminates (split_list_helper A tcast sll') by split_list_helper_total]
                   foralli(fsts:<list A>)(fstspf:{ (fst ! ! (split_list_helper ! t sll')) = fsts }).
                     trans join (fst ! ! (split_list ! l))
                                (fst ! ! (split_list_helper ! l (split_list_length ! l)))
                     trans cong (fst ! ! (split_list_helper ! l *)) sllS
                     trans cong (fst ! ! (split_list_helper ! * (S sll'))) lp
                     trans join (fst ! ! (split_list_helper ! (cons ! h t) (S sll')))
                                (cons ! h (fst ! ! (split_list_helper ! t sll')))
                     trans cong (cons ! h *) fstspf
                           clash (cons ! h fsts)
                                 (nil !)
            end terminates (split_list_length A l) by split_list_length_total
                join (split_list_length ! l) (split_list_length ! l) ]
    end.

Define split_list_length_monotonic : Forall(A:type)
                                           (l:<list A>)
                                           (x:A).
                                       { (or (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l))
                                             (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l)))) = tt } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(x:A).{ (or (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l)))) = tt } with
      nil A' =>
        foralli(x:A).
          abbrev sll_l =  trans cong (split_list_length ! *) lp
                                join (split_list_length ! (nil !)) Z in
          abbrev sll_xl = trans cong (split_list_length ! (cons ! x *)) lp
                                join (split_list_length ! (cons ! x (nil !))) Z in
          symm trans join tt
                          (or tt (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l))))
                     cong (or * (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l))))
                          trans symm [x_eqnat_x terminates (split_list_length A (cons A x l)) by split_list_length_total]
                                cong (eqnat (split_list_length ! (cons ! x l)) *)
                                     symm trans sll_l
                                                symm sll_xl
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(x:A).
          [ induction(t2:<list A>) by t2p t2t IHt2 return Forall(t2pf:{ t = t2 }).{ (or (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l)))) = tt } with
              nil A'' =>
                foralli(t2pf:{ t = t2 }).
                  abbrev tp =  trans t2pf t2p in
                  abbrev lfp = trans lp
                                     cong (cons ! h *) tp in % l = cons h nil
                  abbrev sll_l =  trans cong (split_list_length ! *) lfp
                                        join (split_list_length ! (cons ! h (nil !))) Z in
                  abbrev sll_xl = trans cong (split_list_length ! (cons ! x *)) lfp
                                        join (split_list_length ! (cons ! x (cons ! h (nil !)))) (S Z) in
                  symm trans symm [or_def2 terminates (eqnat terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                             terminates (split_list_length A l) by split_list_length_total)
                                           by eqnatTot]
                             cong (or (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) *)
                                  trans symm [x_eqnat_x terminates (split_list_length A (cons A x l)) by split_list_length_total]
                                  trans cong (eqnat (split_list_length ! (cons ! x l)) *) sll_xl
                                        cong (eqnat (split_list_length ! (cons ! x l)) (S *))
                                             symm sll_l
            | cons A'' h' t' =>
                abbrev h'cast = cast h' by symm inj <list *> t2t in
                abbrev t'cast = cast t' by cong <list *> symm inj <list *> t2t in
                foralli(t2pf:{ t = t2 }).
                  abbrev tp =  trans t2pf t2p in
                  abbrev lfp = trans lp
                                     cong (cons ! h *) tp in % l = cons h (cons h' t')

                  % (or (eqnat (split_list_length ! l) (split_list_length ! t))
                  %     (eqnat (split_list_length ! l) (S (split_list_length ! t)))) = tt
                  abbrev or_ih_l = symm trans symm [IHl tcast hcast]
                                              cong (or (eqnat (split_list_length ! *) (split_list_length ! t)) (eqnat (split_list_length ! *) (S (split_list_length ! t))))
                                                   symm lp in

                  % (or (eqnat (split_list_length ! t) (split_list_length ! t'))
                  %     (eqnat (split_list_length ! t) (S (split_list_length ! t')))) = tt
                  abbrev or_ih_t = symm trans symm [IHl t'cast h'cast]
                                              cong (or (eqnat (split_list_length ! *) (split_list_length ! t')) (eqnat (split_list_length ! *) (S (split_list_length ! t'))))
                                                   symm tp in

                  % (split_list_length ! l) = (S (split_list_length ! t'))
                  abbrev sll_l_eq_S_sll_t' = trans cong (split_list_length ! *) lfp
                                                   join (split_list_length ! (cons ! h (cons ! h' t')))
                                                        (S (split_list_length ! t')) in

                  abbrev G_LEFT1  = terminates (split_list_length A (cons A x l)) by split_list_length_total in
                  abbrev G_LEFT2  = terminates (split_list_length A l) by split_list_length_total in
                  abbrev G_LEFT   = terminates (eqnat G_LEFT1 G_LEFT2) by eqnatTot in
                  abbrev G_RIGHT1 = G_LEFT1 in
                  abbrev G_RIGHT2 = (S G_LEFT2) in
                  abbrev G_RIGHT  = terminates (eqnat G_RIGHT1 G_RIGHT2) by eqnatTot in
                  abbrev GOAL     = terminates (or G_LEFT G_RIGHT) by or_total in

                  %% prove { GOAL = tt } by contradiction
                  [ induction(z:bool) by zp zt IHz return Forall(zpf:{ GOAL = z }).{ GOAL = tt } with
                      ff =>
                        foralli(zpf:{ GOAL = z }).
                          abbrev GOALp = trans zpf zp in % GOAL = ff

                          % if GOAL is ff, then both eqnats are ff
                          abbrev eqnat1ff = [or_ff G_LEFT G_RIGHT GOALp] in % G_LEFT = ff
                          abbrev eqnat2ff = [or_ffr G_LEFT G_RIGHT GOALp] in % G_RIGHT = ff
                          abbrev neq1 = [eqnatNeq G_LEFT1 G_LEFT2 eqnat1ff] in % G_LEFT1 != G_LEFT2
                          abbrev neq2 = [eqnatNeq G_RIGHT1 G_RIGHT2 eqnat2ff] in % G_RIGHT1 != G_RIGHT2

                          % now we know (split_list_length ! (cons ! x l)) != (split_list_length ! l)
                          %         AND (split_list_length ! (cons ! x l)) != (S (split_list_length ! l))

                          % by cong     (split_list_length ! (cons ! x (cons ! h t))) != (split_list_length ! l)
                          %         AND (split_list_length ! (cons ! x (cons ! h t))) != (S (split_list_length ! l))
                          abbrev cpf = cong (split_list_length ! (cons ! x *)) symm lp in
                          abbrev neq1c = trans cpf neq1 in
                          abbrev neq2c = trans cpf neq2 in

                          % by join     (S (split_list_length ! t)) != (split_list_length ! l)
                          %         AND (S (split_list_length ! t)) != (S (split_list_length ! l))
                          abbrev jpf = join (S (split_list_length ! t))
                                            (split_list_length ! (cons ! x (cons ! h t))) in
                          abbrev neq1j = trans jpf neq1c in
                          abbrev neq2j = trans jpf neq2c in

                          % drop S      (S (split_list_length ! t)) != (split_list_length ! l)
                          %         AND (split_list_length ! t)     != (split_list_length ! l)
                          abbrev neq1S = neq1j in
                          abbrev neq2S = [Sneq_neq terminates (split_list_length A tcast) by split_list_length_total
                                                   terminates (split_list_length A l) by split_list_length_total
                                                   neq2j] in

                          % we have from above
                          %    (or (eqnat (split_list_length ! l) (split_list_length ! t))
                          %        (eqnat (split_list_length ! l) (S (split_list_length ! t)))) = tt
                          % so split into cases
                          % 1. (split_list_length ! l) = (split_list_length ! t)  -->  contra
                          % 2. (split_list_length ! l) = (S (split_list_length ! t))  --> contra
                          [ induction(zz:bool) by zzp zzt IHzz return Forall(zzpf:{ (eqnat (split_list_length ! l) (split_list_length ! t)) = zz }).{ GOAL = tt } with
                              ff =>
                                foralli(zzpf:{ (eqnat (split_list_length ! l) (split_list_length ! t)) = zz }).
                                  % (eqnat (split_list_length ! l) (S (split_list_length ! t))) = tt
                                  abbrev rhs_tt = symm trans symm or_ih_l
                                                       trans cong (or * (eqnat (split_list_length ! l) (S (split_list_length ! t))))
                                                                  trans zzpf zzp
                                                             join (or ff (eqnat (split_list_length ! l) (S (split_list_length ! t))))
                                                                  (eqnat (split_list_length ! l) (S (split_list_length ! t))) in
                                  contra trans [eqnatEq terminates (split_list_length A l) by split_list_length_total
                                                        (S terminates (split_list_length A tcast) by split_list_length_total) rhs_tt]
                                               neq1S
                                    { GOAL = tt }
                            | tt =>
                                foralli(zzpf:{ (eqnat (split_list_length ! l) (split_list_length ! t)) = zz }).
                                  contra trans [eqnatEq terminates (split_list_length A l) by split_list_length_total
                                                        terminates (split_list_length A tcast) by split_list_length_total trans zzpf zzp]
                                               neq2S
                                    { GOAL = tt }
                            end terminates (eqnat terminates (split_list_length A l) by split_list_length_total
                                                  terminates (split_list_length A tcast) by split_list_length_total) by eqnatTot
                                join (eqnat (split_list_length ! l) (split_list_length ! t)) (eqnat (split_list_length ! l) (split_list_length ! t)) ]
                    | tt => % trivial case
                        foralli(zpf:{ GOAL = z }).
                          trans zpf zp
                    end GOAL join GOAL GOAL ]
            end tcast join t t ]
    end.

Define split_list_nonnil_snd : Forall(A:type)
                                     (l:<list A>)
                                     (lne:{ l != (nil !) }).
                                 { (snd ! ! (split_list ! l)) != (nil !) } :=
  foralli(A:type)(l:<list A>)(lne:{ l != (nil !) }).
    abbrev l1 = terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot in
    abbrev l2 = terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot in

    % (append A l1 l2) = l
    abbrev append_l1_l2_is_l = [append_split_list A l] in

    % (lt (split_list_length ! l) (list_length ! l)) = tt
    abbrev sll_lt_ll = [split_len_lt_len A l lne] in

    % (lt (split_list_length ! l) (list_length ! (fst ! ! (split_list_helper ! l (split_list_length ! l))))) = ff
    abbrev sll_nlt_ll_fst = [split_list_len_fst_le_n A l terminates (split_list_length A l) by split_list_length_total] in

    % (le (list_length ! l1) (split_list_length ! l)) = tt
    abbrev ll_fst_le_sll = symm trans symm [lt_ff_implies_le terminates (split_list_length A l) by split_list_length_total
                                                             terminates (list_length A terminates (fst <list A> <list A> terminates (split_list_helper A l terminates (split_list_length A l)
                                                                                                                                                                       by split_list_length_total)
                                                                                                                                     by split_list_helper_total)
                                                                                                   by fstTot)
                                                                         by list_length_total
                                                             sll_nlt_ll_fst]
                                      cong (le (list_length ! (fst ! ! *)) (split_list_length ! l))
                                           join (split_list_helper ! l (split_list_length ! l))
                                                (split_list ! l) in

    % (list_length ! l) = (plus (list_length ! l1) (list_length ! l2))
    abbrev ll_is_plus = symm trans symm [append_length A l1 l2]
                                   cong (list_length ! *) append_l1_l2_is_l in

    % now, ll_fst <= sll < ll
    % (lt (list_length ! l1) (list_length ! l)) = tt
    abbrev ll_fst_lt_ll = [lelt_trans terminates (list_length A terminates (fst <list A> <list A>
                                                                                terminates (split_list A l)
                                                                                            by split_list_total)
                                                                            by fstTot)
                                                  by list_length_total
                                      terminates (split_list_length A l) by split_list_length_total
                                      terminates (list_length A l) by list_length_total
                                      ll_fst_le_sll
                                      sll_lt_ll] in

    existse [lt_implies_plus terminates (list_length A l1) by list_length_total
                             terminates (list_length A l) by list_length_total
                             ll_fst_lt_ll]
      foralli(c:nat)(v:{ c != Z })(cpf:{ (plus (list_length ! l1) c) = (list_length ! l) }).
        abbrev len2_nonzero = trans symm [plus_inj2 terminates (list_length A l1) by list_length_total
                                                    c
                                                    terminates (list_length A l2) by list_length_total
                                                    trans cpf ll_is_plus]
                                    v in
        [list_length_nonzero_implies_nonnil A l2 len2_nonzero].

Define split_list_snd_length_monotonic : Forall(A:type)
                                               (l:<list A>)
                                               (x:A).
                                           { (or (eqnat (list_length ! (snd ! ! (split_list ! l))) (list_length ! (snd ! ! (split_list ! (cons ! x l)))))
                                                 (eqnat (S (list_length ! (snd ! ! (split_list ! l)))) (list_length ! (snd ! ! (split_list ! (cons ! x l)))))) = tt } :=
  foralli(A:type)(l:<list A>)(x:A).
    abbrev l1 = terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot in
    abbrev l2 = terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot in

    abbrev xl1 = terminates (fst <list A> <list A> terminates (split_list A (cons A x l)) by split_list_total) by fstTot in
    abbrev xl2 = terminates (snd <list A> <list A> terminates (split_list A (cons A x l)) by split_list_total) by sndTot in

    % (append ! l1 l2) = l
    abbrev append_l1_l2_is_l = [append_split_list A l] in

    % (append ! xl1 xl2) = (cons ! x l)
    abbrev append_xl1_xl2_is_xl = [append_split_list A (cons A x l)] in

    % (list_length ! l) = (plus (list_length ! l1) (list_length ! l2))
    abbrev ll_is_plus = symm trans symm [append_length A l1 l2]
                                   cong (list_length ! *) append_l1_l2_is_l in

    % (list_length ! (fst ! ! (split_list ! l))) = (split_list_length ! l)
    abbrev ll_fst_l = symm trans symm [split_list_len_fst_n A l
                                                            terminates (split_list_length A l) by split_list_length_total
                                                            [le_tt_implies_lt_ff terminates (split_list_length A l) by split_list_length_total
                                                                                 terminates (list_length A l) by list_length_total
                                                                                 [split_len_le_len A l]]]
                                 cong (list_length ! (fst ! ! *))
                                      join (split_list_helper ! l (split_list_length ! l))
                                           (split_list ! l) in

    % (list_length ! (fst ! ! (split_list ! (cons ! x l)))) = (split_list_length ! (cons ! x l))
    abbrev ll_fst_xl = symm trans symm [split_list_len_fst_n A (cons A x l)
                                                             terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                             [le_tt_implies_lt_ff terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                                                  terminates (list_length A (cons A x l)) by list_length_total
                                                                                  [split_len_le_len A (cons A x l)]]]
                                  cong (list_length ! (fst ! ! *))
                                       join (split_list_helper ! (cons ! x l) (split_list_length ! (cons ! x l)))
                                            (split_list ! (cons ! x l)) in

    % (list_length ! l2) = (minus (list_length ! l) (split_list_length ! l))
    abbrev l2len_is_ll_minus_sll = trans symm [append_sublength_l2 A l1 l2]
                                   trans cong (minus (list_length ! *) (list_length ! l1)) append_l1_l2_is_l
                                         cong (minus (list_length ! l) *) ll_fst_l in

    % (list_length ! xl2) = (minus (list_length ! (cons ! x l)) (split_list_length ! (cons ! x l)))
    abbrev xl2len_is_ll_minus_sll = trans symm [append_sublength_l2 A xl1 xl2]
                                    trans cong (minus (list_length ! *) (list_length ! xl1)) append_xl1_xl2_is_xl
                                          cong (minus (list_length ! (cons ! x l)) *) ll_fst_xl in

    % (list_length ! l1) = (split_list_length ! l)
    abbrev l1len_is_lsplitlen = [fst_len_split_list_len A l] in

    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) = z }).
                                              { (or (eqnat (list_length ! l2) (list_length ! xl2))
                                                    (eqnat (S (list_length ! l2)) (list_length ! xl2))) = tt } with
        ff =>
          foralli(zpf:{ (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) = z }).
            % (split_list_length ! (cons ! x l)) = (S (split_list_length ! l))
            abbrev xlsplitlen_is_Slsplitlen = [eqnatEq terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                       (S terminates (split_list_length A l) by split_list_length_total)
                                                       symm trans symm [split_list_length_monotonic A l x]
                                                            trans cong (or * (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l))))
                                                                       trans zpf zp
                                                                  join (or ff (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l))))
                                                                       (eqnat (split_list_length ! (cons ! x l)) (S (split_list_length ! l)))] in

            % (list_length ! l2) = (minus (list_length ! l) (split_list_length ! l))
            %                    = (minus (S (list_length ! l)) (S (split_list_length ! l)))
            %                    = (minus (S (list_length ! l)) (split_list_length ! (cons ! x l)))
            %                    = (minus (list_length ! (cons ! x l)) (split_list_length ! (cons ! x l)))
            %                    = (list_length ! xl2)

            trans cong (or * (eqnat (S (list_length ! l2)) (list_length ! xl2)))
                       [eqEqnat terminates (list_length A l2) by list_length_total
                                terminates (list_length A xl2) by list_length_total
                                trans l2len_is_ll_minus_sll
                                trans join (minus (list_length ! l) (split_list_length ! l))
                                           (minus (S (list_length ! l)) (S (split_list_length ! l)))
                                trans cong (minus (S (list_length ! l)) *)
                                           symm xlsplitlen_is_Slsplitlen
                                trans join (minus (S (list_length ! l)) (split_list_length ! (cons ! x l)))
                                           (minus (list_length ! (cons ! x l)) (split_list_length ! (cons ! x l)))
                                      symm xl2len_is_ll_minus_sll]
                  join (or tt (eqnat (S (list_length ! l2)) (list_length ! xl2)))
                       tt
      | tt =>
          foralli(zpf:{ (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) = z }).
            % (split_list_length ! (cons ! x l)) = (split_list_length ! l)
            abbrev lsplitlen_is_xlsplitlen = symm [eqnatEq terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                           terminates (split_list_length A l) by split_list_length_total
                                                           trans zpf zp] in

            % (S (list_length ! l2)) = (S (minus (list_length ! l) (split_list_length ! l)))
            %                        = (S (minus (list_length ! l) (split_list_length ! (cons ! x l))))
            %                        = (S (minus (S (list_length ! l)) (S (split_list_length ! (cons ! x l)))))
            %                        = (S (minus (list_length ! (cons ! x l)) (S (split_list_length ! (cons ! x l)))))
            %                        = (minus (list_length ! (cons ! x l)) (split_list_length ! (cons ! x l)))
            %                        = (list_length ! xl2)

            trans cong (or (eqnat (list_length ! l2) (list_length ! xl2)) *)
                       [eqEqnat (S terminates (list_length A l2) by list_length_total)
                                terminates (list_length A xl2) by list_length_total
                                trans cong (S *) l2len_is_ll_minus_sll
                                trans cong (S (minus (list_length ! l) *)) lsplitlen_is_xlsplitlen
                                trans join (S (minus (list_length ! l) (split_list_length ! (cons ! x l))))
                                           (S (minus (S (list_length ! l)) (S (split_list_length ! (cons ! x l)))))
                                trans cong (S (minus * (S (split_list_length ! (cons ! x l)))))
                                           join (S (list_length ! l))
                                                (list_length ! (cons ! x l))
                                trans symm [minusS2 terminates (list_length A (cons A x l)) by list_length_total
                                                    terminates (split_list_length A (cons A x l)) by split_list_length_total
                                                    [split_len_lt_len A (cons A x l) clash (cons ! x l) (nil !)]]
                                      symm xl2len_is_ll_minus_sll]
                  [or_def2 terminates (eqnat terminates (list_length A l2) by list_length_total terminates (list_length A xl2) by list_length_total) by eqnatTot]
      end terminates (eqnat terminates (split_list_length A (cons A x l)) by split_list_length_total
                            terminates (split_list_length A l) by split_list_length_total) by eqnatTot
          join (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l))
               (eqnat (split_list_length ! (cons ! x l)) (split_list_length ! l)) ].

Define merge_cons_nonnil1 : Forall(A:type)
                                  (l1 l2:<list A>)
                                  (lne1:{ l1 != (nil !) })
                                  (cmp:Fun(x y:A).bool)
                                  (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                              { (merge ! l1 l2 cmp) != (nil !) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)
                                                        (lne1:{ l1 != (nil !) })
                                                        (cmp:Fun(x y:A).bool)
                                                        (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                    { (merge ! l1 l2 cmp) != (nil !) } with
      nil A1 =>
        foralli(l2:<list A>)(lne1:{ l1 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          contra trans l1p symm lne1
            { (merge ! l1 l2 cmp) != (nil !) }
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(lne1:{ l1 != (nil !) })
                                                            (cmp:Fun(x y:A).bool)
                                                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                        { (merge ! l1 l2 cmp) != (nil !) } with
          nil A2 =>
            foralli(lne1:{ l1 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              trans hypjoin (merge ! l1 l2 cmp)
                            (cons ! h1 t1)
                            by l1p l2p end
                    clash (cons ! h1 t1) (nil !)
        | cons A2 h2 t2 =>
            foralli(lne1:{ l1 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              abbrev h1cast = cast h1 by symm inj <list *> l1t in
              abbrev h2cast = cast h2 by symm inj <list *> l2t in
              abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
              abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
              [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (cmp h1 h2) = z }).{ (merge ! l1 l2 cmp) != (nil !) } with
                  ff =>
                    foralli(zpf:{ (cmp h1 h2) = z }).
                      abbrev cmpff = trans zpf zp in
                      existse [merge_total A t1cast l2 cmp cmp_total]
                        foralli(mo:<list A>)(mopf:{ (merge ! t1 l2 cmp) = mo }).
                          trans hypjoin (merge ! l1 l2 cmp)
                                        (cons ! h1 (merge ! t1 l2 cmp))
                                        by l1p l2p cmpff end
                          trans cong (cons ! h1 *) mopf
                                clash (cons ! h1 mo)
                                      (nil !)
                | tt =>
                    foralli(zpf:{ (cmp h1 h2) = z }).
                      abbrev cmptt = trans zpf zp in
                        trans hypjoin (merge ! l1 l2 cmp)
                                      (cons ! h2 (merge ! l1 t2 cmp))
                                   by l1p l2p cmptt end
                              clash (cons ! h2 terminates (merge A l1 t2 cmp) by [merge_total A l1 t2cast cmp cmp_total])
                                    (nil !)
                end terminates (cmp h1cast h2cast) by cmp_total
                    join (cmp h1 h2) (cmp h1 h2) ]
        end
    end.

Define merge_cons_nonnil2 : Forall(A:type)
                                  (l1 l2:<list A>)
                                  (lne2:{ l2 != (nil !) })
                                  (cmp:Fun(x y:A).bool)
                                  (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                              { (merge ! l1 l2 cmp) != (nil !) } :=
  foralli(A:type)(l1:<list A>).
    induction(l2:<list A>) by l2p l2t IHl2 return Forall(lne2:{ l2 != (nil !) })
                                                        (cmp:Fun(x y:A).bool)
                                                        (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                    { (merge ! l1 l2 cmp) != (nil !) } with
      nil A2 =>
        foralli(lne2:{ l2 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          contra trans l2p symm lne2
            { (merge ! l1 l2 cmp) != (nil !) }
    | cons A2 h2 t2 =>
        [ induction(ll1:<list A>) by ll1p ll1t IHll1 return Forall(ll1pf:{ l1 = ll1 })
                                                                  (lne2:{ l2 != (nil !) })
                                                                  (cmp:Fun(x y:A).bool)
                                                                  (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                              { (merge ! l1 l2 cmp) != (nil !) } with
            nil A1 =>
              foralli(ll1pf:{ l1 = ll1 })(lne2:{ l2 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                abbrev l1p = trans ll1pf ll1p in
                trans hypjoin (merge ! l1 l2 cmp)
                              (cons ! h2 t2)
                              by l1p l2p end
                      clash (cons ! h2 t2) (nil !)
          | cons A1 h1 t1 =>
              foralli(ll1pf:{ l1 = ll1 })(lne2:{ l2 != (nil !) })(cmp:Fun(x y:A).bool)(cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                abbrev l1p = trans ll1pf ll1p in
                abbrev h1cast = cast h1 by symm inj <list *> ll1t in
                abbrev h2cast = cast h2 by symm inj <list *> l2t in
                abbrev t1cast = cast t1 by cong <list *> symm inj <list *> ll1t in
                abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
                [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (cmp h1 h2) = z }).{ (merge ! l1 l2 cmp) != (nil !) } with
                    ff =>
                      foralli(zpf:{ (cmp h1 h2) = z }).
                        abbrev cmpff = trans zpf zp in
                        existse [merge_total A t1cast l2 cmp cmp_total]
                          foralli(mo:<list A>)(mopf:{ (merge ! t1 l2 cmp) = mo }).
                            trans hypjoin (merge ! l1 l2 cmp)
                                          (cons ! h1 (merge ! t1 l2 cmp))
                                          by l1p l2p cmpff end
                            trans cong (cons ! h1 *) mopf
                                  clash (cons ! h1 mo)
                                        (nil !)
                  | tt =>
                      foralli(zpf:{ (cmp h1 h2) = z }).
                        abbrev cmptt = trans zpf zp in
                        existse [merge_total A l1 t2cast cmp cmp_total]
                          foralli(mo:<list A>)(mopf:{ (merge ! l1 t2 cmp) = mo }).
                            trans hypjoin (merge ! l1 l2 cmp)
                                          (cons ! h2 (merge ! l1 t2 cmp))
                                          by l1p l2p cmptt end
                            trans cong (cons ! h2 *) mopf
                                  clash (cons ! h2 mo)
                                        (nil !)
                  end terminates (cmp h1cast h2cast) by cmp_total
                      join (cmp h1 h2) (cmp h1 h2) ]
          end l1 join l1 l1 ]
    end.

Define merge_nil1 : Forall(A:type)
                          (l:<list A>)
                          (cmp:Fun(x y:A).bool).
                      { (merge ! (nil !) l cmp) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(cmp:Fun(x y:A).bool).
                                                { (merge ! (nil !) l cmp) = l } with
      nil A' =>
        foralli(cmp:Fun(x y:A).bool).
          hypjoin (merge ! (nil !) l cmp)
                  l
               by lp end
    | cons A' h t =>
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(cmp:Fun(x y:A).bool).
          hypjoin (merge ! (nil !) l cmp)
                  l
               by lp [IHl tcast cmp] end
    end.

Define merge_nil2 : Forall(A:type)
                          (l:<list A>)
                          (cmp:Fun(x y:A).bool).
                      { (merge ! l (nil !) cmp) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(cmp:Fun(x y:A).bool).
                                                { (merge ! l (nil !) cmp) = l } with
      nil A' =>
        foralli(cmp:Fun(x y:A).bool).
          hypjoin (merge ! l (nil !) cmp)
                  l
               by lp end
    | cons A' h t =>
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(cmp:Fun(x y:A).bool).
          hypjoin (merge ! l (nil !) cmp)
                  l
               by lp [IHl tcast cmp] end
    end.

Define msort_totaln : Forall(A:type)
                            (n:nat)
                            (l:<list A>)
                            (nlen:{ (le (list_length ! l) n) = tt })
                            (cmp:Fun(x y:A).bool)
                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                      Exists(o:<list A>).
                        { (msort ! l cmp) = o } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<list A>)
                                               (nlen:{ (le (list_length ! l) n) = tt })
                                               (cmp:Fun(x y:A).bool)
                                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                         Exists(o:<list A>).
                                           { (msort ! l cmp) = o } with
      Z =>
        foralli(l:<list A>)
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          abbrev ll_Z = [eqnatEq terminates (list_length A l) by list_length_total Z
                                 symm trans symm nlen
                                      trans cong (le (list_length ! l) *) np
                                            [le_Z terminates (list_length A l) by list_length_total]] in
          [ induction(ll:<list A>) by llp llt IHll return Forall(l_ll:{ l = ll }).
                                                          Exists(o:<list A>).
                                                            { (msort ! l cmp) = o } with
              nil A' =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  existsi (nil A)
                          { (msort ! l cmp) = * }
                    hypjoin (msort ! l cmp)
                            (nil !)
                         by lp end
            | cons A' h t =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                  existse [list_length_total A tcast]
                    foralli(tlen:nat)(tlenpf:{ (list_length ! t) = tlen }).
                      contra trans symm ll_Z
                             trans cong (list_length ! *) lp
                             trans join (list_length ! (cons ! h t))
                                        (S (list_length ! t))
                             trans cong (S *) tlenpf
                                   clash (S tlen) Z
                        Exists(o:<list A>).
                          { (msort ! l cmp) = o }
            end l join l l ]
    | S n' =>
        foralli(l:<list A>)
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          [ induction(ll_lt_nv:bool) by ll_lt_nvp ll_lt_nvt IHll_lt_nv return Forall(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                                                                              Exists(o:<list A>).
                                                                                { (msort ! l cmp) = o } with
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

                  [ induction(ll:<list A>) by llp llt IHll return Forall(llpf:{ l = ll }).
                                                                  Exists(o:<list A>).
                                                                    { (msort ! l cmp) = o } with
                      nil A' =>
                        foralli(llpf:{ l = ll }).
                          existsi (nil A)
                                  { (msort ! l cmp) = * }
                            hypjoin (msort ! l cmp)
                                    (nil !)
                                 by trans llpf llp end
                    | cons A' h t =>
                        foralli(llpf:{ l = ll }).
                          abbrev hcast = cast h by symm inj <list *> llt in
                          abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                          [ induction(_tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = _tt }).
                                                                           Exists(o:<list A>).
                                                                             { (msort ! l cmp) = o } with
                              nil A'' =>
                                foralli(ttpf:{ t = _tt }).
                                  % l = (cons ! h (nil !))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  existsi (cons A hcast terminates (msort A (nil A) cmp)
                                                        by existsi (nil A)
                                                                   { (msort ! (nil !) cmp) = * }
                                                             join (msort ! (nil !) cmp) (nil !))
                                          { (msort ! l cmp) = * }
                                    trans cong (msort ! * cmp) lp
                                          join (msort ! (cons ! h (nil !)) cmp)
                                               (cons ! h (msort ! (nil !) cmp))
                            | cons A'' h' t' =>
                                foralli(ttpf:{ t = _tt }).
                                  abbrev h'cast = cast h' by symm inj <list *> ttt in
                                  abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in

                                  % l = (cons ! h (cons ! h' t'))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  abbrev nlen1' = [le_trans terminates (list_length A l1) by list_length_total
                                                            terminates (list_length A l) by list_length_total
                                                            n
                                                            [split_list_le_fst A l]
                                                            nlen] in
                                  abbrev nlen2' = [le_trans terminates (list_length A l2) by list_length_total
                                                            terminates (list_length A l) by list_length_total
                                                            n
                                                            [split_list_le_snd A l]
                                                            nlen] in

                                  existse [IHn n l1 nlen1' cmp cmp_total]
                                    foralli(o1:<list A>)
                                           (opf1:{ (msort ! l1 cmp) = o1 }).
                                      existse [IHn n l2 nlen2' cmp cmp_total]
                                        foralli(o2:<list A>)
                                               (opf2:{ (msort ! l2 cmp) = o2 }).

                                          %- (msort ! l cmp) = (merge ! (msort ! l1 cmp) (msort ! l2 cmp) cmp)
                                          %                  = (merge ! (cons ! x1 (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp))
                                          %                             (cons ! x2 (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp)) cmp) -%

                                          abbrev l1hht = terminates (fst <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by fstTot in
                                          abbrev l2hht = terminates (snd <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by sndTot in

                                          abbrev msort_is_merge_o1_o2 = trans cong (msort ! * cmp) lp
                                                                        trans join (msort ! (cons ! h (cons ! h' t')) cmp)
                                                                                   (merge ! (msort ! l1hht cmp) (msort ! l2hht cmp) cmp)
                                                                        trans cong (merge ! (msort ! (fst ! ! (split_list ! *)) cmp) (msort ! l2hht cmp) cmp) symm lp
                                                                        trans cong (merge ! (msort ! l1 cmp) (msort ! (snd ! ! (split_list ! *)) cmp) cmp) symm lp
                                                                        trans cong (merge ! * (msort ! l2 cmp) cmp) opf1
                                                                              cong (merge ! o1 * cmp) opf2 in
                                          existsi terminates (merge A o1 o2 cmp) by [merge_total A o1 o2 cmp cmp_total]
                                                  { (msort ! l cmp) = * }
                                            msort_is_merge_o1_o2
                          end tcast join t t ]
                    end l join l l ]
            | tt =>
                foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                  abbrev ll_lt_n = trans ll_lt_n_pf ll_lt_nvp in
                  abbrev nlen' = [lt_pred n' n terminates (list_length A l) by list_length_total np ll_lt_n] in
                  [IHn n' l nlen' cmp cmp_total]
            end terminates (lt terminates (list_length A l) by list_length_total n) by lt_total join (lt (list_length A l) n) (lt (list_length A l) n) ]
    end.

Define msort_total : Forall(A:type)
                           (l:<list A>)
                           (cmp:Fun(x y:A).bool)
                           (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                     Exists(o:<list A>).
                           { (msort ! l cmp) = o } :=
  foralli(A:type)
         (l:<list A>)
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev n = (list_length A l) in
    abbrev nlen = [x_le_x terminates (list_length A l) by list_length_total] in
    [msort_totaln A n l nlen cmp cmp_total].

Define msort_cons_nonniln : Forall(A:type)
                                  (n:nat)
                                  (l:<list A>)
                                  (lne:{ l != (nil !) })
                                  (nlen:{ (le (list_length ! l) n) = tt })
                                  (cmp:Fun(x y:A).bool)
                                  (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                              { (msort ! l cmp) != (nil !) } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<list A>)
                                               (lne:{ l != (nil !) })
                                               (nlen:{ (le (list_length ! l) n) = tt })
                                               (cmp:Fun(x y:A).bool)
                                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                           { (msort ! l cmp) != (nil !) } with
      Z =>
        foralli(l:<list A>)
               (lne:{ l != (nil !) })
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          abbrev ll_Z = [eqnatEq terminates (list_length A l) by list_length_total Z
                                 symm trans symm nlen
                                      trans cong (le (list_length ! l) *) np
                                            [le_Z terminates (list_length A l) by list_length_total]] in
          [ induction(ll:<list A>) by llp llt IHll return Forall(l_ll:{ l = ll }).
                                                            { (msort ! l cmp) != (nil !) } with
              nil A' =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  contra trans symm lp lne
                      { (msort ! l cmp) != (nil !) }
            | cons A' h t =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                  existse [list_length_total A tcast]
                    foralli(tlen:nat)(tlenpf:{ (list_length ! t) = tlen }).
                      contra trans symm ll_Z
                             trans cong (list_length ! *) lp
                             trans join (list_length ! (cons ! h t))
                                        (S (list_length ! t))
                             trans cong (S *) tlenpf
                                   clash (S tlen) Z
                          { (msort ! l cmp) != (nil !) }
            end l join l l ]
    | S n' =>
        foralli(l:<list A>)
               (lne:{ l != (nil !) })
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          [ induction(ll_lt_nv:bool) by ll_lt_nvp ll_lt_nvt IHll_lt_nv return Forall(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                                                                                { (msort ! l cmp) != (nil !) } with
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

                  [ induction(ll:<list A>) by llp llt IHll return Forall(llpf:{ l = ll }).
                                                                    { (msort ! l cmp) != (nil !) } with
                      nil A' =>
                        foralli(llpf:{ l = ll }).
                          contra trans llpf
                                 trans llp
                                       symm lne
                              { (msort ! l cmp) != (nil !) }
                    | cons A' h t =>
                        foralli(llpf:{ l = ll }).
                          abbrev hcast = cast h by symm inj <list *> llt in
                          abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                          [ induction(_tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = _tt }).
                                                                             { (msort ! l cmp) != (nil !) } with
                              nil A'' =>
                                foralli(ttpf:{ t = _tt }).
                                  % l = (cons ! h (nil !))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  trans cong (msort ! * cmp) lp
                                  trans join (msort ! (cons ! h (nil !)) cmp)
                                             (cons ! h (nil !))
                                        clash (cons ! h (nil !)) (nil !)
                            | cons A'' h' t' =>
                                foralli(ttpf:{ t = _tt }).
                                  abbrev h'cast = cast h' by symm inj <list *> ttt in
                                  abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in

                                  % l = (cons ! h (cons ! h' t'))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  abbrev lnne = foralli(x:A).trans lp [list_not_length_1 A hcast h'cast t'cast x] in

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

                                  abbrev msort_l1_nonnil = [IHn n l1 lne1' nlen1' cmp cmp_total] in
                                  abbrev msort_l2_nonnil = [IHn n l2 lne2' nlen2' cmp cmp_total] in

                                  %- (msort ! l cmp) = (merge ! (msort ! l1 cmp) (msort ! l2 cmp) cmp)
                                  %                  = (merge ! (cons ! x1 (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp))
                                  %                             (cons ! x2 (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp)) cmp) -%

                                  abbrev l1hht = terminates (fst <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by fstTot in
                                  abbrev l2hht = terminates (snd <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by sndTot in

                                  abbrev msort_is_merge_x1_x2 = trans cong (msort ! * cmp) lp
                                                                trans join (msort ! (cons ! h (cons ! h' t')) cmp)
                                                                           (merge ! (msort ! l1hht cmp) (msort ! l2hht cmp) cmp)
                                                                trans cong (merge ! (msort ! (fst ! ! (split_list ! *)) cmp) (msort ! l2hht cmp) cmp) symm lp
                                                                      cong (merge ! (msort ! l1 cmp) (msort ! (snd ! ! (split_list ! *)) cmp) cmp) symm lp in

                                  existse [msort_total A l1 cmp cmp_total]
                                    foralli(msort_l1:<list A>)(msort_l1pf:{ (msort ! l1 cmp) = msort_l1 }).
                                      existse [msort_total A l2 cmp cmp_total]
                                        foralli(msort_l2:<list A>)(msort_l2pf:{ (msort ! l2 cmp) = msort_l2 }).
                                          existse [nonnil_list_has_head A msort_l1 trans symm msort_l1pf msort_l1_nonnil]
                                            foralli(x1:A)(xt1:<list A>)(x1pf':{ msort_l1 = (cons ! x1 xt1) }).
                                              abbrev x1pf = trans msort_l1pf x1pf' in
                                              existse [nonnil_list_has_head A msort_l2 trans symm msort_l2pf msort_l2_nonnil]
                                                foralli(x2:A)(xt2:<list A>)(x2pf':{ msort_l2 = (cons ! x2 xt2) }).
                                                  abbrev x2pf = trans msort_l2pf x2pf' in
                                                  [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (cmp x1 x2) = z }).
                                                                                            { (msort ! l cmp) != (nil !) } with
                                                      ff =>
                                                        foralli(zpf:{ (cmp x1 x2) = z }).
                                                              abbrev cmpff = trans zpf zp in
                                                              trans msort_is_merge_x1_x2
                                                              trans 
                                                               %- BROKEN HYPJOIN, replaced with trans cong proof below: 
                                                                    hypjoin (merge (msort l1 cmp) (msort l2 cmp) cmp)
                                                                            (cons x1 (merge xt1 (cons x2 xt2) cmp))
                                                                            by x1pf x2pf cmpff end   -% 
                                                                    trans cong (merge * (msort l2 cmp) cmp) x1pf
                                                                    trans cong (merge (cons x1 xt1) * cmp) x2pf
                                                                          hypjoin (merge (cons x1 xt1) (cons x2 xt2) cmp)
                                                                                  (cons x1 (merge xt1 (cons x2 xt2) cmp))
                                                                          by cmpff end 

                                                                clash (cons ! x1 terminates (merge A xt1 (cons A x2 xt2) cmp) 
                                                                                 by [merge_total A xt1 (cons A x2 xt2) cmp cmp_total])
                                                                      (nil !)
                                                    | tt =>
                                                        foralli(zpf:{ (cmp x1 x2) = z }).
                                                          existse [merge_total A (cons A x1 xt1) xt2 cmp cmp_total]
                                                            foralli(omerge:<list A>)(omergepf:{ (merge ! (cons ! x1 xt1) xt2 cmp) = omerge }).
                                                              abbrev cmptt = trans zpf zp in
                                                              trans msort_is_merge_x1_x2
                                                              trans %- BROKEN HYPJOIN:
							            hypjoin (merge ! (msort ! l1 cmp) (msort ! l2 cmp) cmp)
                                                                            (cons ! x2 omerge)
                                                                            by x1pf x2pf cmptt omergepf end -%
                                                                    trans cong (merge * (msort l2 cmp) cmp) x1pf
                                                                    trans cong (merge (cons x1 xt1) * cmp) x2pf
                                                                          hypjoin (merge (cons x1 xt1) (cons x2 xt2) cmp)
                                                                                  (cons x2 omerge)
                                                                          by cmptt omergepf end

                                                                    clash (cons ! x2 omerge)
                                                                          (nil !)
                                                    end terminates (cmp x1 x2) by cmp_total
                                                        join (cmp x1 x2) (cmp x1 x2) ]
                          end tcast join t t ]
                    end l join l l ]
            | tt =>
                foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                  abbrev ll_lt_n = trans ll_lt_n_pf ll_lt_nvp in
                  abbrev nlen' = [lt_pred n' n terminates (list_length A l) by list_length_total np ll_lt_n] in
                  [IHn n' l lne nlen' cmp cmp_total]
            end terminates (lt terminates (list_length A l) by list_length_total n) by lt_total join (lt (list_length A l) n) (lt (list_length A l) n)]
    end.

Define msort_cons_nonnil : Forall(A:type)
                                 (l:<list A>)
                                 (lne:{ l != (nil !) })
                                 (cmp:Fun(x y:A).bool)
                                 (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                             { (msort ! l cmp) != (nil !) } :=
  foralli(A:type)
         (l:<list A>)
         (lne:{ l != (nil !) })
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev n = (list_length A l) in
    abbrev nlen = [x_le_x terminates (list_length A l) by list_length_total] in
    [msort_cons_nonniln A n l lne nlen cmp cmp_total].

% This shows that msort returns a list headed by an element of the
% input.  There's a more accessible version below; this is the
% workhorse.
Define msort_has_headn : Forall(A:type)
                               (n:nat)
                               (l:<list A>)
                               (lne:{ l != (nil !) })
                               (nlen:{ (le (list_length ! l) n) = tt })
                               (cmp:Fun(x y:A).bool)
                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                         Exists(lpair:<pair <list A> <list A>>)
                               (x:A)
                               (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                               (reml:<list A>).
                           { (msort ! l cmp) = (cons ! x reml) } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<list A>)
                                               (lne:{ l != (nil !) })
                                               (nlen:{ (le (list_length ! l) n) = tt })
                                               (cmp:Fun(x y:A).bool)
                                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                         Exists(lpair:<pair <list A> <list A>>)
                                               (x:A)
                                               (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                               (reml:<list A>).
                                           { (msort ! l cmp) = (cons ! x reml) } with
      Z =>
        foralli(l:<list A>)
               (lne:{ l != (nil !) })
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          abbrev ll_Z = [eqnatEq terminates (list_length A l) by list_length_total Z
                                 symm trans symm nlen
                                      trans cong (le (list_length ! l) *) np
                                            [le_Z terminates (list_length A l) by list_length_total]] in
          [ induction(ll:<list A>) by llp llt IHll return Forall(l_ll:{ l = ll }).
                                                          Exists(lpair:<pair <list A> <list A>>)
                                                                (x:A)
                                                                (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                                (reml:<list A>).
                                                            { (msort ! l cmp) = (cons ! x reml) } with
              nil A' =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  contra trans symm lp lne
                    Exists(lpair:<pair <list A> <list A>>)
                          (x:A)
                          (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                          (reml:<list A>).
                      { (msort ! l cmp) = (cons ! x reml) }
            | cons A' h t =>
                foralli(l_ll:{ l = ll }).
                  abbrev lp = trans l_ll llp in
                  abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                  existse [list_length_total A tcast]
                    foralli(tlen:nat)(tlenpf:{ (list_length ! t) = tlen }).
                      contra trans symm ll_Z
                             trans cong (list_length ! *) lp
                             trans join (list_length ! (cons ! h t))
                                        (S (list_length ! t))
                             trans cong (S *) tlenpf
                                   clash (S tlen) Z
                        Exists(lpair:<pair <list A> <list A>>)
                              (x:A)
                              (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                              (reml:<list A>).
                          { (msort ! l cmp) = (cons ! x reml) }
            end l join l l ]
    | S n' =>
        foralli(l:<list A>)
               (lne:{ l != (nil !) })
               (nlen:{ (le (list_length ! l) n) = tt })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          [ induction(ll_lt_nv:bool) by ll_lt_nvp ll_lt_nvt IHll_lt_nv return Forall(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                                                                          Exists(lpair:<pair <list A> <list A>>)
                                                                                (x:A)
                                                                                (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                                                (reml:<list A>).
                                                                            { (msort ! l cmp) = (cons ! x reml) } with
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

                  [ induction(ll:<list A>) by llp llt IHll return Forall(llpf:{ l = ll }).
                                                                  Exists(lpair:<pair <list A> <list A>>)
                                                                        (x:A)
                                                                        (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                                        (reml:<list A>).
                                                                    { (msort ! l cmp) = (cons ! x reml) } with
                      nil A' =>
                        foralli(llpf:{ l = ll }).
                          contra trans llpf
                                 trans llp
                                       symm lne
                            Exists(lpair:<pair <list A> <list A>>)
                                  (x:A)
                                  (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                  (reml:<list A>).
                              { (msort ! l cmp) = (cons ! x reml) }
                    | cons A' h t =>
                        foralli(llpf:{ l = ll }).
                          abbrev hcast = cast h by symm inj <list *> llt in
                          abbrev tcast = cast t by cong <list *> symm inj <list *> llt in
                          [ induction(_tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = _tt }).
                                                                          Exists(lpair:<pair <list A> <list A>>)
                                                                                (x:A)
                                                                                (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                                                (reml:<list A>).
                                                                            { (msort ! l cmp) = (cons ! x reml) } with
                              nil A'' =>
                                foralli(ttpf:{ t = _tt }).
                                  % l = (cons ! h (nil !))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  abbrev lpair = (mkpair <list A> <list A> (nil A) (nil A)) in
                                  existsi lpair
                                          Exists(x:A)
                                                (u:{ l = (append ! (fst ! ! *) (cons ! x (snd ! ! *))) })
                                                (reml:<list A>).
                                            { (msort ! l cmp) = (cons ! x reml) }
                                    existsi hcast
                                            Exists(u:{ l = (append ! (fst ! ! lpair) (cons ! * (snd ! ! lpair))) })
                                                  (reml:<list A>).
                                              { (msort ! l cmp) = (cons ! * reml) }
                                      abbrev u = trans lp
                                                       join (cons ! h (nil !))
                                                            (append ! (fst ! ! lpair) (cons ! h (snd ! ! lpair))) in
                                      existsi u
                                              Exists(reml:<list A>).
                                                { (msort ! l cmp) = (cons ! h reml) }
                                        existsi terminates (msort A terminates (append A terminates (fst <list A> <list A> lpair) by fstTot
                                                                                         terminates (snd <list A> <list A> lpair) by sndTot) by append_total cmp)
                                                        by [msort_total A terminates (append A terminates (fst <list A> <list A> lpair) by fstTot
                                                                                               terminates (snd <list A> <list A> lpair) by sndTot) by append_total
                                                                          cmp cmp_total]
                                                { (msort ! l cmp) = (cons ! h *) }
                                          trans cong (msort ! * cmp) lp
                                                join (msort ! (cons ! h (nil !)) cmp)
                                                     (cons ! h (msort ! (append ! (fst ! ! lpair) (snd ! ! lpair)) cmp))
                            | cons A'' h' t' =>
                                foralli(ttpf:{ t = _tt }).
                                  abbrev h'cast = cast h' by symm inj <list *> ttt in
                                  abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in

                                  % l = (cons ! h (cons ! h' t'))
                                  abbrev lp = trans llpf
                                              trans llp
                                                    cong (cons ! h *)
                                                         trans ttpf ttp in

                                  abbrev lnne = foralli(x:A).trans lp [list_not_length_1 A hcast h'cast t'cast x] in

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

                                  existse [IHn n l1 lne1' nlen1' cmp cmp_total]
                                    foralli(lpair1:<pair <list A> <list A>>)
                                           (x1:A)
                                           (u1:{ l1 = (append ! (fst ! ! lpair1) (cons ! x1 (snd ! ! lpair1))) })
                                           (reml1:<list A>)
                                           (expf1:{ (msort ! l1 cmp) = (cons ! x1 reml1) }).
                                      existse [IHn n l2 lne2' nlen2' cmp cmp_total]
                                        foralli(lpair2:<pair <list A> <list A>>)
                                               (x2:A)
                                               (u2:{ l2 = (append ! (fst ! ! lpair2) (cons ! x2 (snd ! ! lpair2))) })
                                               (reml2:<list A>)
                                               (expf2:{ (msort ! l2 cmp) = (cons ! x2 reml2) }).

                                          %- GOAL:  Exists(lpair:<pair <list A> <list A>>)
                                                          (x:A)
                                                          (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                          (reml:<list A>).
                                                      { (msort ! l cmp) = (cons ! x (msort ! reml cmp)) } -%

                                          %- (msort ! l cmp) = (merge ! (msort ! l1 cmp) (msort ! l2 cmp) cmp)
                                          %                  = (merge ! (cons ! x1 (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp))
                                          %                             (cons ! x2 (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp)) cmp) -%

                                          abbrev l1hht = terminates (fst <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by fstTot in
                                          abbrev l2hht = terminates (snd <list A> <list A> terminates (split_list A (cons A h (cons A h' t'))) by split_list_total) by sndTot in

                                          abbrev msort_is_merge_x1_x2 = trans cong (msort ! * cmp) lp
                                                                        trans join (msort ! (cons ! h (cons ! h' t')) cmp)
                                                                                   (merge ! (msort ! l1hht cmp) (msort ! l2hht cmp) cmp)
                                                                        trans cong (merge ! (msort ! (fst ! ! (split_list ! *)) cmp) (msort ! l2hht cmp) cmp) symm lp
                                                                        trans cong (merge ! (msort ! l1 cmp) (msort ! (snd ! ! (split_list ! *)) cmp) cmp) symm lp
                                                                        trans cong (merge ! * (msort ! l2 cmp) cmp) expf1
                                                                              cong (merge ! (cons ! x1 reml1) * cmp) expf2 in

                                          [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (cmp x1 x2) = z }).
                                                                                  Exists(lpair:<pair <list A> <list A>>)
                                                                                        (x:A)
                                                                                        (u:{ l = (append ! (fst ! ! lpair) (cons ! x (snd ! ! lpair))) })
                                                                                        (reml:<list A>).
                                                                                    { (msort ! l cmp) = (cons ! x reml) } with
                                             ff =>
                                                %- take lpair = (split_list ! (append ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) l2))
                                                %  take x = x1
                                                %  (msort ! l cmp) = (cons ! x1 (merge ! (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp)
                                                %                                        (cons ! x2 (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp)) cmp)
                                                %                  = (cons ! x1 (merge ! (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp)
                                                %                                        (msort ! l2 cmp) cmp)) -%
                                                foralli(zpf:{ (cmp x1 x2) = z }).
                                                  abbrev cmpff = trans zpf zp in
                                                  abbrev lpair = (mkpair <list A> <list A> (fst <list A> <list A> lpair1)
                                                                                           (append A (snd <list A> <list A> lpair1) (append A (fst <list A> <list A> lpair2) (cons A x2 (snd <list A> <list A> lpair2))))) in
                                                  existsi lpair
                                                          Exists(x:A)
                                                                (u:{ l = (append ! (fst ! ! *) (cons ! x (snd ! ! *))) })
                                                                (reml:<list A>).
                                                            { (msort ! l cmp) = (cons ! x reml) }
                                                    existsi x1
                                                            Exists(u:{ l = (append ! (fst ! ! lpair) (cons ! * (snd ! ! lpair))) })
                                                                  (reml:<list A>).
                                                              { (msort ! l cmp) = (cons ! * reml) }
                                                      abbrev u = trans symm [append_split_list A l]
                                                                 trans cong (append ! * l2) u1
                                                                 trans cong (append ! (append ! (fst ! ! lpair1) (cons ! x1 (snd ! ! lpair1))) *) u2
                                                                 trans [append_member_1 A terminates (fst <list A> <list A> lpair1) by fstTot
                                                                                          x1
                                                                                          terminates (snd <list A> <list A> lpair1) by sndTot
                                                                                          terminates (append A terminates (fst <list A> <list A> lpair2) by fstTot (cons A x2 terminates (snd <list A> <list A> lpair2) by sndTot)) by append_total]
                                                                 trans cong (append ! * (cons ! x1 (append ! (snd ! ! lpair1) (append ! (fst ! ! lpair2) (cons ! x2 (snd ! ! lpair2))))))
                                                                            join (fst ! ! lpair1)
                                                                                 (fst ! ! lpair)
                                                                       cong (append ! (fst ! ! lpair) (cons ! x1 *))
                                                                            join (append ! (snd ! ! lpair1) (append ! (fst ! ! lpair2) (cons ! x2 (snd ! ! lpair2))))
                                                                                 (snd ! ! lpair) in
                                                      existsi u
                                                              Exists(reml:<list A>).
                                                                { (msort ! l cmp) = (cons ! x1 reml) }
                                                        existsi terminates (merge A reml1 (cons A x2 reml2) cmp) by [merge_total A reml1 (cons A x2 reml2) cmp cmp_total]
                                                                { (msort ! l cmp) = (cons ! x1 *) }
                                                          trans msort_is_merge_x1_x2
                                                                hypjoin (merge ! (cons ! x1 reml1) (cons ! x2 reml2) cmp)
                                                                        (cons ! x1 (merge ! reml1 (cons ! x2 reml2) cmp))
                                                                        by cmpff end
                                            | tt =>
                                                %- take lpair = (split_list ! (append ! l1 (append ! (fst ! ! lpair2) (snd ! ! lpair2))))
                                                %  take x = x2
                                                %  (msort ! l cmp) = (cons ! x2 (merge ! (cons ! x1 (msort ! (append ! (fst ! ! lpair1) (snd ! ! lpair1)) cmp))
                                                %                                        (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp) cmp))
                                                %                  = (cons ! x2 (merge ! (msort ! l1 cmp)
                                                %                                        (msort ! (append ! (fst ! ! lpair2) (snd ! ! lpair2)) cmp) cmp))-%
                                                foralli(zpf:{ (cmp x1 x2) = z }).
                                                  abbrev cmptt = trans zpf zp in
                                                  abbrev lpair = (mkpair <list A> <list A> (append A (append A (fst <list A> <list A> lpair1) (cons A x1 (snd <list A> <list A> lpair1))) (fst <list A> <list A> lpair2))
                                                                                           (snd <list A> <list A> lpair2)) in
                                                  existsi lpair
                                                          Exists(x:A)
                                                                (u:{ l = (append ! (fst ! ! *) (cons ! x (snd ! ! *))) })
                                                                (reml:<list A>).
                                                            { (msort ! l cmp) = (cons ! x reml) }
                                                    existsi x2
                                                            Exists(u:{ l = (append ! (fst ! ! lpair) (cons ! * (snd ! ! lpair))) })
                                                                  (reml:<list A>).
                                                              { (msort ! l cmp) = (cons ! * reml) }
                                                      abbrev u = trans symm [append_split_list A l]
                                                                 trans cong (append ! * l2) u1
                                                                 trans cong (append ! (append ! (fst ! ! lpair1) (cons ! x1 (snd ! ! lpair1))) *) u2
                                                                 trans [append_member_2 A terminates (append A terminates (fst <list A> <list A> lpair1) by fstTot (cons A x1 terminates (snd <list A> <list A> lpair1) by sndTot)) by append_total
                                                                                          terminates (fst <list A> <list A> lpair2) by fstTot
                                                                                          x2
                                                                                          terminates (snd <list A> <list A> lpair2) by sndTot]
                                                                 trans cong (append ! * (cons ! x2 (snd ! ! lpair2)))
                                                                            join (append ! (append ! (fst ! ! lpair1) (cons ! x1 (snd ! ! lpair1))) (fst ! ! lpair2))
                                                                                 (fst ! ! lpair)
                                                                       cong (append ! (fst ! ! lpair) (cons ! x2 *))
                                                                            join (snd ! ! lpair2)
                                                                                 (snd ! ! lpair) in
                                                      existsi u
                                                              Exists(reml:<list A>).
                                                                { (msort ! l cmp) = (cons ! x2 reml) }
                                                        existsi terminates (merge A (cons A x1 reml1) reml2 cmp) by [merge_total A (cons A x1 reml1) reml2 cmp cmp_total]
                                                                { (msort ! l cmp) = (cons ! x2 *) }
                                                          trans msort_is_merge_x1_x2
                                                                hypjoin (merge ! (cons ! x1 reml1) (cons ! x2 reml2) cmp)
                                                                        (cons ! x2 (merge ! (cons ! x1 reml1) reml2 cmp))
                                                                        by cmptt end
                                            end terminates (cmp x1 x2) by cmp_total
                                                join (cmp x1 x2) (cmp x1 x2) ]
                          end tcast join t t ]
                    end l join l l ]
            | tt =>
                foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                  abbrev ll_lt_n = trans ll_lt_n_pf ll_lt_nvp in
                  abbrev nlen' = [lt_pred n' n terminates (list_length A l) by list_length_total np ll_lt_n] in
                  [IHn n' l lne nlen' cmp cmp_total]
            end terminates (lt terminates (list_length A l) by list_length_total n) by lt_total join (lt (list_length A l) n) (lt (list_length A l) n)]
    end.

% This shows that msort returns a list headed by an element of the
% input.  This version just heads up the induction of msort_has_headn.
Define msort_has_head : Forall(A:type)
                              (l:<list A>)
                              (lne:{ l != (nil !) })
                              (cmp:Fun(x y:A).bool)
                              (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                        Exists(lpair:<pair <list A> <list A>>)
                              (x:A)
                              (u:{ l = (append A (fst ! ! lpair) (cons A x (snd ! ! lpair))) })
                              (reml:<list A>).
                          { (msort ! l cmp) = (cons ! x reml) } :=
  foralli(A:type)
         (l:<list A>)
         (lne:{ l != (nil !) })
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev n = (list_length A l) in
    abbrev nlen = [x_le_x terminates (list_length A l) by list_length_total] in
    [msort_has_headn A n l lne nlen cmp cmp_total].

Define merge_length : Forall(A:type)
                            (l1 l2:<list A>)
                            (cmp:Fun(x y:A).bool)
                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                        { (list_length ! (merge ! l1 l2 cmp)) = (plus (list_length ! l1) (list_length ! l2)) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)
                                                        (cmp:Fun(x y:A).bool)
                                                        (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                    { (list_length ! (merge ! l1 l2 cmp)) = (plus (list_length ! l1) (list_length ! l2)) } with
      nil A1 =>
        foralli(l2:<list A>)
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          trans cong (list_length ! (merge ! * l2 cmp)) l1p
          trans cong (list_length ! *)
                     [merge_nil1 A l2 cmp]
                symm trans cong (plus (list_length ! *) (list_length ! l2)) l1p
                           join (plus (list_length ! (nil !)) (list_length ! l2))
                                (list_length ! l2)
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(cmp:Fun(x y:A).bool)
                                                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                        { (list_length ! (merge ! l1 l2 cmp)) = (plus (list_length ! l1) (list_length ! l2)) } with
          nil A2 =>
            foralli(cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              trans cong (list_length ! (merge ! l1 * cmp)) l2p
              trans cong (list_length ! *)
                         [merge_nil2 A l1 cmp]
                    symm trans cong (plus (list_length ! l1) (list_length ! *)) l2p
                         trans join (plus (list_length ! l1) (list_length ! (nil !)))
                                    (plus (list_length ! l1) Z)
                               [plusZ terminates (list_length A l1) by list_length_total]
        | cons A2 h2 t2 =>
            foralli(cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              abbrev h1cast = cast h1 by symm inj <list *> l1t in
              abbrev h2cast = cast h2 by symm inj <list *> l2t in
              abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
              abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
              [ induction(c:bool) by cp ct IHc return Forall(cpf:{ (cmp h1 h2) = c }).
                                                        { (list_length ! (merge ! l1 l2 cmp)) = (plus (list_length ! l1) (list_length ! l2)) } with
                  ff =>
                    foralli(cpf:{ (cmp h1 h2) = c }).
                      trans cong (list_length ! (merge ! * l2 cmp)) l1p
                      trans cong (list_length ! (merge ! (cons ! h1 t1) * cmp)) l2p
                      trans hypjoin (list_length ! (merge ! (cons ! h1 t1) (cons ! h2 t2) cmp))
                                    (S (list_length ! (merge ! t1 l2 cmp)))
                                 by trans cpf cp
                                    symm l2p end
                      trans cong (S *)
                                 [IHl1 t1cast l2 cmp cmp_total]
                            symm trans cong (plus (list_length ! *) (list_length ! l2)) l1p
                                       join (plus (list_length ! (cons ! h1 t1)) (list_length ! l2))
                                            (S (plus (list_length ! t1) (list_length ! l2)))
                | tt =>
                    foralli(cpf:{ (cmp h1 h2) = c }).
                      trans cong (list_length ! (merge ! * l2 cmp)) l1p
                      trans cong (list_length ! (merge ! (cons ! h1 t1) * cmp)) l2p
                      trans hypjoin (list_length ! (merge ! (cons ! h1 t1) (cons ! h2 t2) cmp))
                                    (S (list_length ! (merge ! l1 t2 cmp)))
                                 by trans cpf cp
                                    symm l1p end
                      trans cong (S *)
                                 [IHl2 t2cast cmp cmp_total]
                            symm trans cong (plus (list_length ! l1) (list_length ! *)) l2p
                                 trans join (plus (list_length ! l1) (list_length ! (cons ! h2 t2)))
                                            (plus (list_length ! l1) (S (list_length ! t2)))
                                       [plusS terminates (list_length A l1) by list_length_total
                                              terminates (list_length A t2cast) by list_length_total]
                end terminates (cmp h1cast h2cast) by cmp_total
                    join (cmp h1 h2) (cmp h1 h2) ]
        end
    end.

Define msort_lengthn : Forall(A:type)
                             (n:nat)
                             (l:<list A>)
                             (nlen:{ (le (list_length ! l) n) = tt })
                             (cmp:Fun(x y:A).bool)
                             (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                         { (list_length ! l) = (list_length ! (msort ! l cmp)) } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<list A>)
                                               (nlen:{ (le (list_length ! l) n) = tt })
                                               (cmp:Fun(x y:A).bool)
                                               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                           { (list_length ! l) = (list_length ! (msort ! l cmp)) } with
      Z =>
        induction(l:<list A>) by lp lt_ IHl return Forall(nlen:{ (le (list_length ! l) n) = tt })
                                                         (cmp:Fun(x y:A).bool)
                                                         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                     { (list_length ! l) = (list_length ! (msort ! l cmp)) } with
          nil A' =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              hypjoin (list_length ! l)
                      (list_length ! (msort ! l cmp))
                   by lp end
        | cons A' h t =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              abbrev tcast = cast t by cong <list *> symm inj <list *> lt_ in
              abbrev ll_Z = [eqnatEq terminates (list_length A l) by list_length_total Z
                                     symm trans symm nlen
                                          trans cong (le (list_length ! l) *) np
                                                [le_Z terminates (list_length A l) by list_length_total]] in
              existse [list_length_total A tcast]
                foralli(tlen:nat)(tlenpf:{ (list_length ! t) = tlen }).
                  contra trans symm ll_Z
                         trans cong (list_length ! *) lp
                         trans join (list_length ! (cons ! h t))
                                    (S (list_length ! t))
                         trans cong (S *) tlenpf
                               clash (S tlen) Z
                    { (list_length ! l) = (list_length ! (msort ! l cmp)) }
        end
    | S n' =>
        induction(l:<list A>) by lp lt_ IHl return Forall(nlen:{ (le (list_length ! l) n) = tt })
                                                         (cmp:Fun(x y:A).bool)
                                                         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                     { (list_length ! l) = (list_length ! (msort ! l cmp)) } with
          nil A' =>
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
            abbrev nlen' = trans cong (le (list_length ! *) n') lp
                           trans join (le (list_length ! (nil !)) n')
                                      (le Z n')
                                 [Z_le n'] in
            [IHn n' l nlen' cmp cmp_total]
        | cons A' h t =>
            abbrev hcast = cast h by symm inj <list *> lt_ in
            abbrev tcast = cast t by cong <list *> symm inj <list *> lt_ in
            foralli(nlen:{ (le (list_length ! l) n) = tt })
                   (cmp:Fun(x y:A).bool)
                   (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              [ induction(tt_:<list A>) by tt_p tt_t IHtt_ return Forall(tt_pf:{ t = tt_ }).
                                                                { (list_length ! l) = (list_length ! (msort ! l cmp)) } with
                  nil A'' =>
                    foralli(tt_pf:{ t = tt_ }).
                      hypjoin (list_length ! l)
                              (list_length ! (msort ! l cmp))
                           by lp trans tt_pf tt_p end
                | cons A'' h' t' =>
                    foralli(tt_pf:{ t = tt_ }).
                      [ induction(ll_lt_nv:bool) by ll_lt_nvp ll_lt_nvt IHll_lt_nv return Forall(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                                                                                            { (list_length ! l) = (list_length ! (msort ! l cmp)) } with
                          ff =>
                            foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                              abbrev h'cast = cast h' by symm inj <list *> tt_t in
                              abbrev t'cast = cast t' by cong <list *> symm inj <list *> tt_t in

                              % l = (cons ! h (cons ! h' t'))
                              abbrev lfullp = trans lp
                                                    cong (cons ! h *)
                                                         trans tt_pf tt_p in

                              abbrev l1 = terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot in
                              abbrev l2 = terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot in

                              abbrev nlen1' = [le_trans terminates (list_length A l1) by list_length_total
                                                        terminates (list_length A l) by list_length_total
                                                        n
                                                        [split_list_le_fst A l]
                                                        nlen] in
                              abbrev nlen2' = [le_trans terminates (list_length A l2) by list_length_total
                                                        terminates (list_length A l) by list_length_total
                                                        n
                                                        [split_list_le_snd A l]
                                                        nlen] in
                              symm trans cong (list_length ! (msort ! * cmp)) lfullp
                                   trans join (list_length ! (msort ! (cons ! h (cons ! h' t')) cmp))
                                              (list_length ! (merge ! (msort ! (fst ! ! (split_list ! (cons ! h (cons ! h' t')))) cmp) (msort ! (snd ! ! (split_list ! (cons ! h (cons ! h' t')))) cmp) cmp))
                                   trans cong (list_length ! (merge ! (msort ! (fst ! ! (split_list ! *)) cmp) (msort ! (snd ! ! (split_list ! *)) cmp) cmp)) symm lfullp
                                   trans [merge_length A terminates (msort A terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot cmp)
                                                         by [msort_total A terminates (fst <list A> <list A> terminates (split_list A l) by split_list_total) by fstTot cmp cmp_total]
                                                         terminates (msort A terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot cmp)
                                                         by [msort_total A terminates (snd <list A> <list A> terminates (split_list A l) by split_list_total) by sndTot cmp cmp_total]
                                                       cmp cmp_total]
                                   trans cong (plus * (list_length ! (msort ! l2 cmp)))
                                              symm [IHl l1 nlen1' cmp cmp_total]
                                   trans cong (plus (list_length ! l1) *)
                                              symm [IHl l2 nlen2' cmp cmp_total]
                                   trans symm [append_length A l1 l2]
                                         cong (list_length ! *)
                                              [append_split_list A l]
                        | tt =>
                            foralli(ll_lt_n_pf:{ (lt (list_length ! l) n) = ll_lt_nv }).
                              abbrev ll_lt_n = trans ll_lt_n_pf ll_lt_nvp in
                              abbrev nlen' = [lt_pred n' n terminates (list_length A l) by list_length_total np ll_lt_n] in
                              [IHn n' l nlen' cmp cmp_total]
                        end terminates (lt terminates (list_length A l) by list_length_total n) by lt_total
                            join (lt (list_length ! l) n) (lt (list_length ! l) n)]
                end tcast join t t ]
        end
    end.

Define msort_length : Forall(A:type)
                            (l:<list A>)
                            (cmp:Fun(x y:A).bool)
                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                        { (list_length ! l) = (list_length ! (msort ! l cmp)) } :=
  foralli(A:type)
         (l:<list A>)
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev n = (list_length A l) in
    abbrev nlen = [x_le_x terminates (list_length A l) by list_length_total] in
    [msort_lengthn A n l nlen cmp cmp_total].

Define msort_nonnil : Forall(A:type)
                            (l:<list A>)
                            (lne:{ l != (nil !) })
                            (cmp:Fun(x y:A).bool)
                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                        { (msort ! l cmp) != (nil !) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) })
                                                    (cmp:Fun(x y:A).bool)
                                                    (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                                { (msort ! l cmp) != (nil !) } with
      nil A' =>
        foralli(lne:{ l != (nil !) }).
          contra trans lp
                       symm lne
            Forall(cmp:Fun(x y:A).bool)
                  (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
              { (msort ! l cmp) != (nil !) }
    | cons A' h t =>
        foralli(lne:{ l != (nil !) })
               (cmp:Fun(x y:A).bool)
               (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
          [ induction(o:<list A>) by op ot IHo return Forall(opf:{ (msort ! l cmp) = o }).
                                                        { (msort ! l cmp) != (nil !) } with
              nil A'' =>
                foralli(opf:{ (msort ! l cmp) = o }).
                  contra trans hypjoin (S (list_length ! t))
                                       (list_length ! l)
                                    by lp end
                         trans [msort_length A l cmp cmp_total]
                         trans %- BROKEN HYPJOIN:
                               hypjoin (list_length ! (msort ! l cmp))
                                       Z
                                    by trans opf op end -%
                               trans cong (list_length *) trans opf op
                                     join (list_length nil) Z
                               clash Z (S terminates (list_length ! t) by list_length_total)
                    { (msort ! l cmp) != (nil !) }
            | cons A'' h' t' =>
                foralli(opf:{ (msort ! l cmp) = o }).
                  trans opf
                  trans op
                        clash (cons ! h' t')
                              (nil !)
            end terminates (msort A l cmp) by [msort_total A l cmp cmp_total]
                join (msort ! l cmp) (msort ! l cmp) ]
    end.
