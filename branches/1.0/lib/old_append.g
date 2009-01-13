Define append : Fun(A:type)(l1 l2 : <list A>).<list A> :=
	fun append(A:type)(l1 l2 : <list A>) : <list A>.
	match l1 by u v return <list A> with
	  nil A' => l2
	| cons A' a' l1' =>
             cast (cons A' a'
                      (append A' l1'
		         cast l2 by cong <list *> inj <list *> v))
	     by cong <list *> symm inj <list *> v
    end.

Define append_nil : Forall(A:type)(l:<list A>).{ (append A l (nil A)) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (append A l (nil A)) = l } with
      nil A' =>      trans cong (append A' * (nil A')) lp
                     trans join (append A' (nil A') (nil A')) (nil A')
                           symm lp
    | cons A' h t => abbrev t' = cast t by cong <list *> symm inj <list *> lt in
                     trans cong (append * l (nil *)) symm inj <list *> symm lt
                     trans cong (append A' * (nil A')) lp
                     trans join (append A' (cons A' h t) (nil A')) (cons A' h (append A' t (nil A')))
                     trans cong (cons A' h *) [IHl t']
                           symm lp
    end.

Define append_total : Forall(A:type)(l1 l2:<list A>).Exists(l3:<list A>).{ (append ! l1 l2) = l3 } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>).Exists(l3:<list A>).{ (append ! l1 l2) = l3 } with
      nil A' =>
        foralli(l2:<list A>).
          existsi l2 { (append ! l1 l2) = * }
            trans cong (append ! * l2) l1p
                  join (append ! (nil !) l2) l2
    | cons A' h t =>
        foralli(l2:<list A>).
          abbrev hcast = cast h by symm inj <list *> l1t in
          abbrev tcast = cast t by cong <list *> symm inj <list *> l1t in

          existse [IHl1 tcast l2]
            foralli(l3:<list A>)(l3pf:{ (append ! t l2) = l3 }).
              existsi (cons A hcast l3) { (append ! l1 l2) = * }
                trans cong (append ! * l2) l1p
                trans join (append ! (cons ! h t) l2)
                           (cons ! h (append ! t l2))
                      cong (cons ! h *) l3pf
    end.

Define append_nonnil : Forall(A:type)(l1 l2:<list A>)(u:{ l2 != (nil !) }).{ (append ! l1 l2) != (nil !) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)(u:{ l2 != (nil !) }).{ (append ! l1 l2) != (nil !) } with
      nil A' =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(u:{ l2 != (nil !) }).{ (append ! l1 l2) != (nil !) } with
          nil A'' =>
            foralli(u:{ l2 != (nil !) }).
              contra trans l2p symm u
                { (append ! l1 l2) != (nil !) }
        | cons A'' h' t' =>
            foralli(u:{ l2 != (nil !) }).
              trans cong (append ! * l2) l1p
              trans join (append ! (nil !) l2)
                         l2
              trans l2p
                    clash (cons ! h' t')
                          (nil !)
        end
    | cons A' h t =>
        foralli(l2:<list A>)(u:{ l2 != (nil !) }).
          trans cong (append ! * l2) l1p
          trans join (append ! (cons ! h t) l2)
                     (cons ! h (append ! t l2))
                clash (cons ! h terminates (append ! t l2) by append_total)
                      (nil !)
    end.

Define append_appendf : Forall(A:type)(l1 l2:<list A>).{ (append ! l1 l2) = (appendf ! l1 l2) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>).{ (append ! l1 l2) = (appendf ! l1 l2) } with
      nil A1 =>
        foralli(l2:<list A>).
          hypjoin (append ! l1 l2)
                  (appendf ! l1 l2)
               by l1p end
    | cons A1 h1 t1 =>
        foralli(l2:<list A>).
          abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
          trans hypjoin (append ! l1 l2)
                        (cons ! h1 (append ! t1 l2))
                     by l1p end
          trans cong (cons ! h1 *)
                     [IHl1 t1cast l2]
                hypjoin (cons ! h1 (appendf ! t1 l2))
                        (appendf ! l1 l2)
                     by l1p end
    end.

Define appendf_append : Forall(A:type)(l1 l2:<list A>).{ (appendf ! l1 l2) = (append ! l1 l2) } :=
  foralli(A:type)(l1 l2:<list A>).
    symm [append_appendf A l1 l2].

Define append_length : Forall(A:type)(l1 l2:<list A>).{ (list_length ! (append ! l1 l2)) = (plus (list_length ! l1) (list_length ! l2)) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>).{ (list_length ! (append ! l1 l2)) = (plus (list_length ! l1) (list_length ! l2)) } with
      nil A1 =>
        foralli(l2:<list A>).
          abbrev l1_len_zero = trans cong (list_length ! *) l1p
                                     join (list_length ! (nil !)) Z in
          abbrev plus_l1_l2_is_l2 = trans cong (plus * (list_length ! l2)) l1_len_zero
                                          join (plus Z (list_length ! l2))
                                               (list_length ! l2) in
          trans cong (list_length ! (append ! * l2)) l1p
          trans join (list_length ! (append ! (nil !) l2))
                     (list_length ! l2)
                symm plus_l1_l2_is_l2
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return { (list_length ! (append ! l1 l2)) = (plus (list_length ! l1) (list_length ! l2)) } with
          nil A2 =>
            abbrev l2_len_zero = trans cong (list_length ! *) l2p
                                       join (list_length ! (nil !)) Z in
            abbrev plus_l1_l2_is_l1 = trans cong (plus (list_length A l1) *) l2_len_zero
                                            [plusZ terminates (list_length A l1) by list_length_total] in
            trans cong (list_length ! *)
                       trans cong (append ! l1 *) l2p
                             [append_nil A l1]
                  symm plus_l1_l2_is_l1
        | cons A2 h2 t2 =>
            % (list_length ! (append ! t1 l2)) = (plus (list_length ! t1) (list_length ! l2))
            abbrev ih = [IHl1 cast t1 by cong <list *> symm inj <list *> l1t l2] in

            symm trans cong (plus (list_length ! *) (list_length ! l2)) l1p
                 trans join (plus (list_length ! (cons ! h1 t1)) (list_length ! l2))
                            (S (plus (list_length ! t1) (list_length ! l2)))
                 trans cong (S *) symm ih
                 trans join (S (list_length ! (append ! t1 l2)))
                            (list_length ! (append ! (cons ! h1 t1) l2))
                       cong (list_length ! (append ! * l2)) symm l1p
        end
    end.

Define append_sublength_l1 : Forall(A:type)(l1 l2:<list A>).{ (minus (list_length ! (append ! l1 l2)) (list_length ! l2)) = (list_length ! l1) } :=
  foralli(A:type)(l1 l2:<list A>).
    trans cong (minus * (list_length ! l2))
               [append_length A l1 l2]
          [minus_plus2 terminates (list_length A l1) by list_length_total
                       terminates (list_length A l2) by list_length_total].

Define append_sublength_l2 : Forall(A:type)(l1 l2:<list A>).{ (minus (list_length ! (append ! l1 l2)) (list_length ! l1)) = (list_length ! l2) } :=
  foralli(A:type)(l1 l2:<list A>).
    trans cong (minus * (list_length ! l1))
               [append_length A l1 l2]
          [minus_plus1 terminates (list_length A l1) by list_length_total
                       terminates (list_length A l2) by list_length_total].

Define append_assoc : Forall(A:type)(l1 l2 l3:<list A>).{ (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2 l3:<list A>).{ (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
      nil A1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(l3:<list A>).{ (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
          nil A2 =>
            induction(l3:<list A>) by l3p l3t IHl3 return { (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
              nil A3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (nil !) (append ! * l3)) l2p
                trans cong (append ! (nil !) (append ! (nil !) *)) l3p
                trans join (append ! (nil !) (append ! (nil !) (nil !)))
                           (append ! (append ! (nil !) (nil !)) (nil !))
                trans cong (append ! (append ! * (nil !)) (nil !)) symm l1p
                trans cong (append ! (append ! l1 *) (nil !)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            | cons A3 h3 t3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (nil !) (append ! * l3)) l2p
                trans cong (append ! (nil !) (append ! (nil !) *)) l3p
                trans join (append ! (nil !) (append ! (nil !) (cons ! h3 t3)))
                           (append ! (append ! (nil !) (nil !)) (cons ! h3 t3))
                trans cong (append ! (append ! * (nil !)) (cons ! h3 t3)) symm l1p
                trans cong (append ! (append ! l1 *) (cons ! h3 t3)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            end
        | cons A2 h2 t2 =>
            induction(l3:<list A>) by l3p l3t IHl3 return { (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
              nil A3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (nil !) (append ! * l3)) l2p
                trans cong (append ! (nil !) (append ! (cons ! h2 t2) *)) l3p
                trans join (append ! (nil !) (append ! (cons ! h2 t2) (nil !)))
                           (append ! (append ! (nil !) (cons ! h2 t2)) (nil !))
                trans cong (append ! (append ! * (cons ! h2 t2)) (nil !)) symm l1p
                trans cong (append ! (append ! l1 *) (nil !)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            | cons A3 h3 t3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (nil !) (append ! * l3)) l2p
                trans cong (append ! (nil !) (append ! (cons ! h2 t2) *)) l3p
                trans join (append ! (nil !) (append ! (cons ! h2 t2) (cons ! h3 t3)))
                           (append ! (append ! (nil !) (cons ! h2 t2)) (cons ! h3 t3))
                trans cong (append ! (append ! * (cons ! h2 t2)) (cons ! h3 t3)) symm l1p
                trans cong (append ! (append ! l1 *) (cons ! h3 t3)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            end
        end
    | cons A1 h1 t1 =>
        abbrev h1cast = cast h1 by symm inj <list *> l1t in
        abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(l3:<list A>).{ (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
          nil A2 =>
            induction(l3:<list A>) by l3p l3t IHl3 return { (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
              nil A3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (cons ! h1 t1) (append ! * l3)) l2p
                trans cong (append ! (cons ! h1 t1) (append ! (nil !) *)) l3p
                trans join (append ! (cons ! h1 t1) (append ! (nil !) (nil !)))
                           (append ! (cons ! h1 t1) (nil !))
                trans symm [append_nil A terminates (append A (cons A h1cast t1cast) (nil A)) by append_total]
                trans cong (append ! (append ! * (nil !)) (nil !)) symm l1p
                trans cong (append ! (append ! l1 *) (nil !)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            | cons A3 h3 t3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (cons ! h1 t1) (append ! * l3)) l2p
                trans cong (append ! (cons ! h1 t1) (append ! (nil !) *)) l3p
                trans join (append ! (cons ! h1 t1) (append ! (nil !) (cons ! h3 t3)))
                           (append ! (cons ! h1 t1) (cons ! h3 t3))
                trans cong (append ! * (cons ! h3 t3))
                      symm [append_nil A (cons A h1cast t1cast)]
                trans cong (append ! (append ! * (nil !)) (cons ! h3 t3)) symm l1p
                trans cong (append ! (append ! l1 *) (cons ! h3 t3)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            end
        | cons A2 h2 t2 =>
            abbrev h2cast = cast h2 by symm inj <list *> l2t in
            abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
            induction(l3:<list A>) by l3p l3t IHl3 return { (append ! l1 (append ! l2 l3)) = (append ! (append ! l1 l2) l3) } with
              nil A3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans cong (append ! (cons ! h1 t1) (append ! * l3)) l2p
                trans cong (append ! (cons ! h1 t1) (append ! (cons ! h2 t2) *)) l3p
                trans cong (append ! (cons ! h1 t1) *)
                           [append_nil A (cons A h2cast t2cast)]
                trans symm [append_nil A terminates (append A (cons A h1cast t1cast) (cons A h2cast t2cast)) by append_total]
                trans cong (append ! (append ! * (cons ! h2 t2)) (nil !)) symm l1p
                trans cong (append ! (append ! l1 *) (nil !)) symm l2p
                      cong (append ! (append ! l1 l2) *) symm l3p
            | cons A3 h3 t3 =>
                trans cong (append ! * (append ! l2 l3)) l1p
                trans join (append ! (cons ! h1 t1) (append ! l2 l3))
                           (cons ! h1 (append ! t1 (append ! l2 l3)))
                trans cong (cons ! h1 *)
                           [IHl1 t1cast l2 l3]
                trans join (cons ! h1 (append ! (append ! t1 l2) l3))
                           (append ! (append ! (cons ! h1 t1) l2) l3)
                      cong (append ! (append ! * l2) l3) symm l1p
            end
        end
    end.

Define append_member_1 : Forall(A:type)(l1:<list A>)(h1:A)(t1 l2:<list A>).{ (append ! (append ! l1 (cons ! h1 t1)) l2) = (append ! l1 (cons ! h1 (append ! t1 l2))) } :=
  foralli(A:type)(l1:<list A>)(h1:A)(t1 l2:<list A>).
    trans symm [append_assoc A l1 (cons A h1 t1) l2]
          join (append ! l1 (append ! (cons ! h1 t1) l2))
               (append ! l1 (cons ! h1 (append ! t1 l2))).

Define append_member_2 : Forall(A:type)(l1 l2:<list A>)(h2:A)(t2:<list A>).{ (append ! l1 (append ! l2 (cons ! h2 t2))) = (append ! (append ! l1 l2) (cons ! h2 t2)) } :=
  foralli(A:type)(l1 l2:<list A>)(h2:A)(t2:<list A>).
    [append_assoc A l1 l2 (cons A h2 t2)].



Define skip_last_last : Forall(A:type)(l:<list A>)(lne:{ l != (nil !) }).{ (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !))) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) }).{ (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !))) = l } with
      nil A' =>
        foralli(lne:{ l != (nil !) }).
          contra trans lp
                       symm lne
            { (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !))) = l }
    | cons A' h t =>
        foralli(lne:{ l != (nil !) }).
          abbrev hcast = cast h by symm inj <list *> lt in
          abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
          [ induction(tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = tt }).{ (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !))) = l } with
              nil A'' =>
                foralli(ttpf:{ t = tt }).
                  hypjoin (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !)))
                          l
                       by lp
                          trans ttpf ttp end
            | cons A'' h' t' =>
                foralli(ttpf:{ t = tt }).
                  abbrev tne = trans ttpf
                               trans ttp
                                     clash (cons ! h' t') (nil !) in
                  trans hypjoin (append ! (skip_last_elt ! l) (cons ! (last_elt ! l) (nil !)))
                                (append ! (skip_last_elt ! (cons ! h t)) (cons ! (last_elt ! t) (nil !)))
                             by lp
                                trans ttpf ttp end
                  trans cong (append ! * (cons ! (last_elt ! t) (nil !)))
                             trans cong (skip_last_elt ! (cons ! h *)) trans ttpf ttp
                             trans join (skip_last_elt ! (cons ! h (cons ! h' t')))
                                        (cons ! h (skip_last_elt ! (cons ! h' t')))
                                   cong (cons ! h (skip_last_elt ! *)) symm trans ttpf ttp
                  trans join (append ! (cons ! h (skip_last_elt ! t)) (cons ! (last_elt ! t) (nil !)))
                             (cons ! h (append ! (skip_last_elt ! t) (cons ! (last_elt ! t) (nil !))))
                  trans cong (cons ! h *)
                             [IHl tcast tne]
                        symm lp
            end tcast
                join t t ]
    end.
