Include "../lib/option.g".
Include "pml_proofs.g".

%% LIST MEMBERSHIP

Define list_memberf_f : Fun(A:type)
                           (x:A)
                           (eqA:Fun(x y:A).bool)
                           (h:A)
                           (b:bool).bool :=
  fun(A:type)(x:A)(eqA:Fun(x y:A).bool)(h:A)(b:bool).
  (or b (eqA x h)).

Define list_memberf : Fun(A:type)
                         (x:A)
                         (l:<list A>)
                         (eqA:Fun(x y:A).bool).bool :=
  fun(A:type)(x:A)(l:<list A>)(eqA:Fun(x y:A).bool).
  (foldr A bool (list_memberf_f A x eqA) ff l).

Define list_memberf_f_total : Forall(A:type)
                                    (x:A)
                                    (eqA:Fun(x y:A).bool)
                                    (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z })
                                    (h:A)
                                    (b:bool).
                              Exists(o:bool).
                                { (list_memberf_f ! x eqA h b) = o } :=
  foralli(A:type)
         (x:A)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z })
         (h:A)
         (b:bool).
    existsi terminates (or b terminates (eqA x h) by eqA_total) by or_total
            { (list_memberf_f ! x eqA h b) = * }
      join (list_memberf_f ! x eqA h b)
           (or b (eqA x h)).

Define list_memberf_f_partapp_total : Forall(A:type)
                                            (x:A)
                                            (eqA:Fun(x y:A).bool).
                                      Exists(f:Fun(h:A)(b:bool).bool).
                                       { (list_memberf_f ! x eqA) = f } :=
  foralli(A:type)
         (x:A)
         (eqA:Fun(x y:A).bool).
    abbrev f = fun(h:A)(b:bool).
               (or b (eqA x h)) in
    existsi f
            { (list_memberf_f ! x eqA) = * }
      join (list_memberf_f ! x eqA)
           f.

Define list_memberf_total : Forall(A:type)
                                  (x:A)
                                  (l:<list A>)
                                  (eqA:Fun(x y:A).bool)
                                  (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z }).
                              Exists(o:bool).
                                { (list_memberf ! x l eqA) = o } :=
  foralli(A:type)
         (x:A)
         (l:<list A>)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z }).
    existse [foldrTot A bool terminates (list_memberf_f A x eqA) by list_memberf_f_partapp_total
                             [list_memberf_f_total A x eqA eqA_total] ff l]
      foralli(o:bool)(opf:{ (foldr ! ! (list_memberf_f ! x eqA) ff l) = o }).
        existsi o
                { (list_memberf ! x l eqA) = * }
          trans join (list_memberf ! x l eqA)
                     (foldr ! ! (list_memberf_f A x eqA) ff l)
                opf.

Define msort_preserves_list_memberf : Forall(A:type)
                                            (x:A)
                                            (l:<list A>)
                                            (eqA:Fun(x y:A).bool)
                                            (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
                                            (cmp:Fun(x y:A).bool)
                                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                        { (list_memberf ! x l eqA) = (list_memberf ! x (msort ! l cmp) eqA) } :=
  foralli(A:type)
         (x:A)
         (l:<list A>)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev f = (list_memberf_f A x eqA) in
    abbrev ftot = [list_memberf_f_total A x eqA eqA_total] in
    abbrev fcomm0 = foralli(b:bool)(a1 a2:A).
                      trans join (f a2 (f a1 b))
                                 (or (or b (eqA x a1)) (eqA x a2))
                      trans [or_assoc b terminates (eqA x a1) by eqA_total terminates (eqA x a2) by eqA_total]
                      trans cong (or b *)
                                 [or_comm terminates (eqA x a1) by eqA_total terminates (eqA x a2) by eqA_total]
                      trans symm [or_assoc b terminates (eqA x a2) by eqA_total terminates (eqA x a1) by eqA_total]
                            join (or (or b (eqA x a2)) (eqA x a1))
                                 (f a1 (f a2 b)) in
    abbrev fcomm = foralli(x:A)(b:bool)(l1 l2:<list A>).[strengthen_comm A bool x l1 l2 f b fcomm0 ftot] in
    trans join (list_memberf ! x l eqA)
               (foldr ! ! f ff l)
    trans [foldr_pf2 A bool f l ff fcomm ftot cmp cmp_total]
          join (foldr ! ! f ff (msort ! l cmp))
               (list_memberf ! x (msort ! l cmp) eqA).

%% (MULTI)LIST COUNT

Define list_counteltf_f : Fun(A:type)
                             (x:A)
                             (eqA:Fun(x y:A).bool)
                             (h:A)
                             (n:nat).nat :=
  fun(A:type)(x:A)(eqA:Fun(x y:A).bool)(h:A)(n:nat).
  match (eqA x h) with
    ff => n
  | tt => (S n)
  end.

Define list_counteltf : Fun(A:type)
                           (x:A)
                           (l:<list A>)
                           (eqA:Fun(x y:A).bool).nat :=
  fun(A:type)(x:A)(l:<list A>)(eqA:Fun(x y:A).bool).
  (foldr A nat (list_counteltf_f A x eqA) Z l).

Define list_counteltf_f_total : Forall(A:type)
                                      (x:A)
                                      (eqA:Fun(x y:A).bool)
                                      (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z })
                                      (h:A)
                                      (n:nat).
                                Exists(m:nat).
                                  { (list_counteltf_f ! x eqA h n) = m } :=
  foralli(A:type)
         (x:A)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z })
         (h:A)
         (n:nat).
    [ induction(b:bool) by bp bt IHb return Forall(bpf:{ (eqA x h) = b }).
                                            Exists(m:nat).
                                              { (list_counteltf_f ! x eqA h n) = m } with
        ff =>
          foralli(bpf:{ (eqA x h) = b }).
            existsi n
                    { (list_counteltf_f ! x eqA h n) = * }
              hypjoin (list_counteltf_f ! x eqA h n)
                      n
                   by trans bpf bp end
      | tt =>
          foralli(bpf:{ (eqA x h) = b }).
            existsi (S n)
                    { (list_counteltf_f ! x eqA h n) = * }
              hypjoin (list_counteltf_f ! x eqA h n)
                      (S n)
                   by trans bpf bp end
      end terminates (eqA x h) by eqA_total
          join (eqA x h) (eqA x h) ].

Define list_counteltf_f_partapp_total : Forall(A:type)
                                              (x:A)
                                              (eqA:Fun(x y:A).bool).
                                        Exists(f:Fun(h:A)(n:nat).nat).
                                          { (list_counteltf_f ! x eqA) = f } :=
  foralli(A:type)
         (x:A)
         (eqA:Fun(x y:A).bool).
    abbrev f = fun(h:A)(n:nat).
               match (eqA x h) with
                 ff => n
               | tt => (S n)
               end in
    existsi f
            { (list_counteltf_f ! x eqA) = * }
      join (list_counteltf_f ! x eqA)
           f.

Define list_counteltf_total : Forall(A:type)
                                    (x:A)
                                    (l:<list A>)
                                    (eqA:Fun(x y:A).bool)
                                    (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z }).
                              Exists(m:nat).
                                { (list_counteltf ! x l eqA) = m } :=
  foralli(A:type)
         (x:A)
         (l:<list A>)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(z:bool).{ (eqA x y) = z }).
    existse [foldrTot A nat terminates (list_counteltf_f A x eqA) by list_counteltf_f_partapp_total
                            [list_counteltf_f_total A x eqA eqA_total] Z l]
      foralli(m:nat)(mpf:{ (foldr ! ! (list_counteltf_f ! x eqA) Z l) = m }).
        existsi m
                { (list_counteltf ! x l eqA) = * }
          trans join (list_counteltf ! x l eqA)
                     (foldr ! ! (list_counteltf_f A x eqA) Z l)
                mpf.

Define list_counteltf_f_simple_comm : Forall(A:type)
                                            (x:A)
                                            (eqA:Fun(x y:A).bool)
                                            (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
                                            (b:nat)
                                            (a1 a2:A).
                                        { (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b)) = (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b)) } :=
  foralli(A:type)
         (x:A)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
         (b:nat)
         (a1 a2:A).
    [ induction(e1:bool) by e1p e1t IHe1 return Forall(e1pf:{ (eqA x a1) = e1 }).
                                                  { (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b)) = (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b)) } with
        ff =>
          foralli(e1pf:{ (eqA x a1) = e1 }).
            [ induction(e2:bool) by e2p e2t IHe2 return Forall(e2pf:{ (eqA x a2) = e2 }).
                                                          { (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b)) = (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b)) } with
                ff =>
                  foralli(e2pf:{ (eqA x a2) = e2 }).
                    hypjoin (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b))
                            (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b))
                         by trans e1pf e1p
                            trans e2pf e2p end
              | tt =>
                  foralli(e2pf:{ (eqA x a2) = e2 }).
                    hypjoin (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b))
                            (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b))
                         by trans e1pf e1p
                            trans e2pf e2p end
              end terminates (eqA x a2) by eqA_total
                  join (eqA x a2) (eqA x a2) ]
      | tt =>
          foralli(e1pf:{ (eqA x a1) = e1 }).
            [ induction(e2:bool) by e2p e2t IHe2 return Forall(e2pf:{ (eqA x a2) = e2 }).
                                                          { (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b)) = (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b)) } with
                ff =>
                  foralli(e2pf:{ (eqA x a2) = e2 }).
                    hypjoin (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b))
                            (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b))
                         by trans e1pf e1p
                            trans e2pf e2p end
              | tt =>
                  foralli(e2pf:{ (eqA x a2) = e2 }).
                    hypjoin (list_counteltf_f A x eqA a2 (list_counteltf_f A x eqA a1 b))
                            (list_counteltf_f A x eqA a1 (list_counteltf_f A x eqA a2 b))
                         by trans e1pf e1p
                            trans e2pf e2p end
              end terminates (eqA x a2) by eqA_total
                  join (eqA x a2) (eqA x a2) ]
      end terminates (eqA x a1) by eqA_total
          join (eqA x a1) (eqA x a1) ].

Define msort_preserves_list_counteltf : Forall(A:type)
                                              (x:A)
                                              (l:<list A>)
                                              (eqA:Fun(x y:A).bool)
                                              (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
                                              (cmp:Fun(x y:A).bool)
                                              (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                          { (list_counteltf ! x l eqA) = (list_counteltf ! x (msort ! l cmp) eqA) } :=
  foralli(A:type)
         (x:A)
         (l:<list A>)
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(b:bool).{ (eqA x y) = b })
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev f = (list_counteltf_f A x eqA) in
    abbrev ftot = [list_counteltf_f_total A x eqA eqA_total] in
    abbrev fcomm0 = [list_counteltf_f_simple_comm A x eqA eqA_total] in
    abbrev fcomm = foralli(x:A)(b:nat)(l1 l2:<list A>).[strengthen_comm A nat x l1 l2 f b fcomm0 ftot] in
    trans join (list_counteltf ! x l eqA)
               (foldr ! ! f Z l)
    trans [foldr_pf2 A nat f l Z fcomm ftot cmp cmp_total]
          join (foldr ! ! f Z (msort ! l cmp))
               (list_counteltf ! x (msort ! l cmp) eqA).

%% LIST LENGTH

Define list_lengthf : Fun(A:type)
                         (l:<list A>).nat :=
  fun(A:type)(l:<list A>).
  abbrev list_lengthf_f = fun(h:A)(n:nat).(S n) in
  (foldr A nat list_lengthf_f Z l).

Define list_lengthf_total : Forall(A:type)
                                  (l:<list A>).
                            Exists(n:nat).
                              { (list_lengthf ! l) = n } :=
  foralli(A:type)(l:<list A>).
    abbrev list_lengthf_f = fun(h:A)(n:nat).(S n) in
    abbrev list_lengthf_f_total = foralli(h:A)(n:nat).existsi (S n) { (list_lengthf_f h n) = * } join (list_lengthf_f h n) (S n) in
    existse [foldrTot A nat list_lengthf_f list_lengthf_f_total Z l]
      foralli(n:nat)(npf:{ (foldr ! ! list_lengthf_f Z l) = n }).
        existsi n
                { (list_lengthf ! l) = * }
          trans join (list_lengthf ! l)
                     (foldr ! ! list_lengthf_f Z l)
                npf.

Define msort_preserves_list_lengthf : Forall(A:type)
                                            (l:<list A>)
                                            (cmp:Fun(x y:A).bool)
                                            (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
                                        { (list_lengthf ! l) = (list_lengthf ! (msort ! l cmp)) } :=
  foralli(A:type)
         (l:<list A>)
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(b:bool).{ (cmp x y) = b }).
    abbrev f = fun(h:A)(n:nat).(S n) in
    abbrev ftot = foralli(h:A)(n:nat).existsi (S n) { (f h n) = * } join (f h n) (S n) in
    abbrev fcomm0 = foralli(n:nat)(a1 a2:A).
                      join (f a2 (f a1 n))
                           (f a1 (f a2 n)) in
    abbrev fcomm = foralli(x:A)(n:nat)(l1 l2:<list A>).[strengthen_comm A nat x l1 l2 f n fcomm0 ftot] in
    trans join (list_lengthf ! l)
               (foldr ! ! f Z l)
    trans [foldr_pf2 A nat f l Z fcomm ftot cmp cmp_total]
          join (foldr ! ! f Z (msort ! l cmp))
               (list_lengthf ! (msort ! l cmp)).

%% list min/max

Define list_minf_f : Fun(A:type)
                        (cmp:Fun(x y:A).bool)
                        (x:A)(y:<option A>).<option A> :=
  fun(A:type)
     (cmp:Fun(x y:A).bool)
     (x:A)(y:<option A>).
  match y by yp yt return <option A> with
    nothing A' =>
      (something A x)
  | something A' y' =>
      abbrev y'cast = cast y' by symm inj <option *> yt in
      match (cmp x y'cast) return <option A> with
        ff => (something A x)
      | tt => y
      end
  end.

Define list_minf_f_is_something : Forall(A:type)
                                        (cmp:Fun(x y:A).bool)
                                        (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                        (x:A)(y:<option A>).
                                    { (list_minf_f ! cmp x y) != (nothing !) } :=
  foralli(A:type)
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
         (x:A).
    induction(y:<option A>) by yp yt IHy return { (list_minf_f ! cmp x y) != (nothing !) } with
      nothing A' =>
        trans hypjoin (list_minf_f ! cmp x y)
                      (something ! x)
                   by yp end
              clash (something ! x)
                    (nothing !)
    | something A' y' =>
        abbrev y'cast = cast y' by symm inj <option *> yt in
        [ induction(c:bool) by cp ct IHc return Forall(cpf:{ (cmp x y') = c }).
                                                  { (list_minf_f ! cmp x y) != (nothing !) } with
            ff =>
              foralli(cpf:{ (cmp x y') = c }).
                trans hypjoin (list_minf_f ! cmp x y)
                              (something ! x)
                           by yp
                              trans cpf cp end
                      clash (something ! x)
                            (nothing !)
          | tt =>
              foralli(cpf:{ (cmp x y') = c }).
                trans hypjoin (list_minf_f ! cmp x y)
                              (something ! y')
                           by yp
                              trans cpf cp end
                      clash (something ! y')
                            (nothing !)
          end terminates (cmp x y'cast) by cmp_total
              join (cmp x y') (cmp x y') ]
    end.

Define list_minf_f_partapp_total : Forall(A:type)
                                         (cmp:Fun(x y:A).bool).
                                   Exists(f:Fun(x:A)(y:<option A>).<option A>).
                                     { (list_minf_f ! cmp) = f } :=
  foralli(A:type)
         (cmp:Fun(x y:A).bool).
    abbrev f = fun(x:A)(y:<option A>).
               match y by yp yt return <option A> with
                 nothing A' =>
                   (something A x)
               | something A' y' =>
                   abbrev y'cast = cast y' by symm inj <option *> yt in
                   match (cmp x y'cast) return <option A> with
                     ff => (something A x)
                   | tt => y
                   end
               end in
    existsi f
            { (list_minf_f ! cmp) = * }
      join (list_minf_f ! cmp)
           f.

Define list_minf_f_total : Forall(A:type)
                                 (cmp:Fun(x y:A).bool)
                                 (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                 (x:A)(y:<option A>).
                           Exists(o:<option A>).
                             { (list_minf_f ! cmp x y) = o } :=
  foralli(A:type)
         (cmp:Fun(x y:A).bool)
         (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
         (x:A).
    induction(y:<option A>) by yp yt IHy return Exists(o:<option A>).
                                                  { (list_minf_f ! cmp x y) = o } with
      nothing A' =>
        existsi (something A x)
                { (list_minf_f ! cmp x y) = * }
          hypjoin (list_minf_f ! cmp x y)
                  (something A x)
               by yp end
    | something A' y' =>
        abbrev y'cast = cast y' by symm inj <option *> yt in
        [ induction(c:bool) by cp ct IHc return Forall(cpf:{ (cmp x y') = c }).
                                                Exists(o:<option A>).
                                                  { (list_minf_f ! cmp x y) = o } with
            ff =>
              foralli(cpf:{ (cmp x y') = c }).
                existsi (something A x)
                        { (list_minf_f ! cmp x y) = * }
                  hypjoin (list_minf_f ! cmp x y)
                          (something A x)
                       by yp
                          trans cpf cp end
          | tt =>
              foralli(cpf:{ (cmp x y') = c }).
                existsi y
                        { (list_minf_f ! cmp x y) = * }
                  hypjoin (list_minf_f ! cmp x y)
                          y
                       by yp
                          trans cpf cp end
          end terminates (cmp x y'cast) by cmp_total
              join (cmp x y') (cmp x y') ]
    end.

Define list_minf_f_simple_comm : Forall(A:type)
                                       (cmp:Fun(x y:A).bool)
                                       (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
                                       (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                       (x y:A).
                                   { (list_minf_f ! cmp x (something ! y)) = (list_minf_f ! cmp y (something ! x)) } :=
  foralli(A:type)
         (cmp:Fun(x y:A).bool)
         (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
         (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
         (x y:A).
    [ induction(c:bool) by cp ct IHc return Forall(cpf:{ (cmp x y) = c }).
                                              { (list_minf_f ! cmp x (something ! y)) = (list_minf_f ! cmp y (something ! x)) } with
        ff =>
          foralli(cpf:{ (cmp x y) = c }).
            abbrev xy_x = hypjoin (list_minf_f ! cmp x (something ! y))
                                  (something ! x)
                               by trans cpf cp end in
            [ induction(d:bool) by dp dt IHd return Forall(dpf:{ (cmp y x) = d }).
                                                      { (list_minf_f ! cmp x (something ! y)) = (list_minf_f ! cmp y (something ! x)) } with
                ff =>
                  foralli(dpf:{ (cmp y x) = d }).
                    trans xy_x
                    trans cong (something ! *)
                               [cmp_eq x y trans cpf trans cp symm trans dpf dp]
                          hypjoin (something ! y)
                                  (list_minf_f ! cmp y (something ! x))
                               by trans dpf dp end
              | tt =>
                  foralli(dpf:{ (cmp y x) = d }).
                    trans xy_x
                          hypjoin (something ! x)
                                  (list_minf_f ! cmp y (something ! x))
                               by trans dpf dp end
              end terminates (cmp y x) by cmp_total
                  join (cmp y x) (cmp y x) ]
      | tt =>
          foralli(cpf:{ (cmp x y) = c }).
            abbrev xy_y = hypjoin (list_minf_f ! cmp x (something ! y))
                                  (something ! y)
                               by trans cpf cp end in
            [ induction(d:bool) by dp dt IHd return Forall(dpf:{ (cmp y x) = d }).
                                                      { (list_minf_f ! cmp x (something ! y)) = (list_minf_f ! cmp y (something ! x)) } with
                ff =>
                  foralli(dpf:{ (cmp y x) = d }).
                    trans xy_y
                          hypjoin (something ! y)
                                  (list_minf_f ! cmp y (something ! x))
                               by trans dpf dp end
              | tt =>
                  foralli(dpf:{ (cmp y x) = d }).
                    trans xy_y
                    trans cong (something ! *)
                               symm [cmp_eq x y trans cpf trans cp symm trans dpf dp]
                          hypjoin (something ! x)
                                  (list_minf_f ! cmp y (something ! x))
                               by trans dpf dp end
              end terminates (cmp y x) by cmp_total
                  join (cmp y x) (cmp y x) ]
      end terminates (cmp x y) by cmp_total
          join (cmp x y) (cmp x y) ].

Define list_minf_f_comm : Forall(A:type)
                                (cmp:Fun(x y:A).bool)
                                (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
                                (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
                                (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
                                (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                (eqA:Fun(x y:A).bool)
                                (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
                                (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
                                (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y })
                                (x y:A)(z:<option A>).
                            { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } :=
  foralli(A:type)
         (cmp:Fun(x y:A).bool)
         (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
         (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
         (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
         (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
         (eqA:Fun(x y:A).bool)
         (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
         (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
         (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y })
         (x y:A).
    induction(z:<option A>) by zp zt IHz return { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
      nothing A' =>
        trans cong (list_minf_f ! cmp x *)
                   hypjoin (list_minf_f ! cmp y z)
                           (something ! y)
                        by zp end
        trans [list_minf_f_simple_comm A cmp cmp_eq cmp_total x y]
              cong (list_minf_f ! cmp y *)
                   hypjoin (something ! x)
                           (list_minf_f ! cmp x z)
                        by zp end
    | something A' z' =>
        abbrev z'cast = cast z' by symm inj <option *> zt in
        [ induction(c1:bool) by c1p c1t IHc1 return Forall(c1pf:{ (cmp y z') = c1 }).
                                                      { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
            ff =>
              foralli(c1pf:{ (cmp y z') = c1 }).
                abbrev list_minf_f_y_z_is_y = hypjoin (list_minf_f ! cmp y z)
                                                      (something ! y)
                                                   by zp
                                                      trans c1pf c1p end in
                [ induction(c2:bool) by c2p c2t IHc2 return Forall(c2pf:{ (cmp x y) = c2 }).
                                                              { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                    ff =>
                      foralli(c2pf:{ (cmp x y) = c2 }).
                        abbrev cmp_x_z_ff = trans [cmp_trans x y z'cast trans c2pf
                                                                        trans c2p
                                                                              symm trans c1pf
                                                                                         c1p]
                                            trans c2pf
                                                  c2p in
                        abbrev list_minf_f_x_z_is_x = hypjoin (list_minf_f ! cmp x z)
                                                              (something ! x)
                                                           by zp
                                                              cmp_x_z_ff end in
                        [ induction(c3:bool) by c3p c3t IHc3 return Forall(c3pf:{ (eqA x y) = c3 }).
                                                                      { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                            ff =>
                              foralli(c3pf:{ (eqA x y) = c3 }).
                                abbrev cmp_y_x_tt =
                                  [ induction(c4:bool) by c4p c4t IHc4 return Forall(c4pf:{ (cmp y x) = c4 }).
                                                                                { (cmp y x) = tt } with
                                      ff =>
                                        foralli(c4pf:{ (cmp y x) = c4 }).
                                          contra trans c4pf
                                                 trans c4p
                                                 trans symm trans c2pf
                                                                  c2p
                                                       [cmp_inv x y [eqA_neq x y trans c3pf c3p]]
                                            { (cmp y x) = tt }
                                    | tt =>
                                        foralli(c4pf:{ (cmp y x) = c4 }).
                                          trans c4pf c4p
                                    end terminates (cmp y x) by cmp_total
                                        join (cmp y x) (cmp y x) ] in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_y
                                trans hypjoin (list_minf_f ! cmp x (something ! y))
                                              (something ! x)
                                           by trans c2pf c2p end
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_x
                                                 hypjoin (list_minf_f ! cmp y (something ! x))
                                                         (something ! x)
                                                      by cmp_y_x_tt end
                          | tt =>
                              foralli(c3pf:{ (eqA x y) = c3 }).
                                abbrev x_is_y = [eqA_eq x y trans c3pf c3p] in
                                hypjoin (list_minf_f ! cmp x (list_minf_f ! cmp y z))
                                        (list_minf_f ! cmp y (list_minf_f ! cmp x z))
                                     by x_is_y end
                          end terminates (eqA x y) by eqA_total
                              join (eqA x y) (eqA x y) ]
                  | tt =>
                      foralli(c2pf:{ (cmp x y) = c2 }).
                        %% cmp x y = tt
                        %% cmp y z = ff
                        abbrev list_minf_f_x_y_is_y = hypjoin (list_minf_f ! cmp x (something ! y))
                                                              (something ! y)
                                                           by trans c2pf c2p end in
                        [ induction(c3:bool) by c3p c3t IHc3 return Forall(c3pf:{ (cmp x z') = c3 }).
                                                                      { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                            ff =>
                              foralli(c3pf:{ (cmp x z') = c3 }).
                                abbrev list_minf_f_x_z_is_x = hypjoin (list_minf_f ! cmp x z)
                                                                      (something ! x)
                                                                   by zp
                                                                      trans c3pf c3p end in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_y
                                trans list_minf_f_x_y_is_y
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_x
                                           trans [list_minf_f_simple_comm A cmp cmp_eq cmp_total y x]
                                                 list_minf_f_x_y_is_y
                          | tt =>
                              foralli(c3pf:{ (cmp x z') = c3 }).
                                abbrev list_minf_f_x_z_is_z = hypjoin (list_minf_f ! cmp x z)
                                                                      z
                                                                   by zp
                                                                      trans c3pf c3p end in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_y
                                trans list_minf_f_x_y_is_y
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_z
                                                 list_minf_f_y_z_is_y
                          end terminates (cmp x z'cast) by cmp_total
                              join (cmp x z') (cmp x z') ]
                  end terminates (cmp x y) by cmp_total
                      join (cmp x y) (cmp x y) ]
          | tt =>
              foralli(c1pf:{ (cmp y z') = c1 }).
                abbrev list_minf_f_y_z_is_z = hypjoin (list_minf_f ! cmp y z)
                                                      z
                                                   by zp
                                                      trans c1pf c1p end in
                [ induction(c2:bool) by c2p c2t IHc2 return Forall(c2pf:{ (cmp x y) = c2 }).
                                                              { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                    ff =>
                      foralli(c2pf:{ (cmp x y) = c2 }).
                        abbrev list_minf_f_x_y_is_x = hypjoin (list_minf_f ! cmp x (something ! y))
                                                              (something ! x)
                                                           by trans c2pf c2p end in
                        [ induction(c3:bool) by c3p c3t IHc3 return Forall(c3pf:{ (cmp x z') = c3 }).
                                                                      { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                            ff =>
                              foralli(c3pf:{ (cmp x z') = c3 }).
                                abbrev list_minf_f_x_z_is_x = hypjoin (list_minf_f ! cmp x z)
                                                                      (something ! x)
                                                                   by zp
                                                                      trans c3pf c3p end in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_z
                                trans list_minf_f_x_z_is_x
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_x
                                           trans [list_minf_f_simple_comm A cmp cmp_eq cmp_total y x]
                                                 list_minf_f_x_y_is_x
                          | tt =>
                              foralli(c3pf:{ (cmp x z') = c3 }).
                                abbrev list_minf_f_x_z_is_z = hypjoin (list_minf_f ! cmp x z)
                                                                      z
                                                                   by zp
                                                                      trans c3pf c3p end in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_z
                                trans list_minf_f_x_z_is_z
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_z
                                                 list_minf_f_y_z_is_z
                          end terminates (cmp x z'cast) by cmp_total
                              join (cmp x z') (cmp x z') ]
                  | tt =>
                      foralli(c2pf:{ (cmp x y) = c2 }).
                        abbrev cmp_x_z_tt = trans [cmp_trans x y z'cast trans c2pf
                                                                        trans c2p
                                                                              symm trans c1pf
                                                                                         c1p]
                                            trans c2pf
                                                  c2p in
                        abbrev list_minf_f_x_z_is_z = hypjoin (list_minf_f ! cmp x z)
                                                              z
                                                           by zp
                                                              cmp_x_z_tt end in
                        [ induction(c3:bool) by c3p c3t IHc3 return Forall(c3pf:{ (eqA x y) = c3 }).
                                                                      { (list_minf_f ! cmp x (list_minf_f ! cmp y z)) = (list_minf_f ! cmp y (list_minf_f ! cmp x z)) } with
                            ff =>
                              foralli(c3pf:{ (eqA x y) = c3 }).
                                abbrev cmp_y_x_tt =
                                  [ induction(c4:bool) by c4p c4t IHc4 return Forall(c4pf:{ (cmp y x) = c4 }).
                                                                                { (cmp y x) = ff } with
                                      ff =>
                                        foralli(c4pf:{ (cmp y x) = c4 }).
                                          trans c4pf c4p
                                    | tt =>
                                        foralli(c4pf:{ (cmp y x) = c4 }).
                                          contra trans c4pf
                                                 trans c4p
                                                 trans symm trans c2pf
                                                                  c2p
                                                       [cmp_inv x y [eqA_neq x y trans c3pf c3p]]
                                            { (cmp y x) = ff }
                                    end terminates (cmp y x) by cmp_total
                                        join (cmp y x) (cmp y x) ] in
                                trans cong (list_minf_f ! cmp x *)
                                           list_minf_f_y_z_is_z
                                trans hypjoin (list_minf_f ! cmp x z)
                                              z
                                           by list_minf_f_x_z_is_z end
                                      symm trans cong (list_minf_f ! cmp y *)
                                                      list_minf_f_x_z_is_z
                                                 hypjoin (list_minf_f ! cmp y z)
                                                         z
                                                      by zp
                                                         trans c1pf c1p end
                          | tt =>
                              foralli(c3pf:{ (eqA x y) = c3 }).
                                abbrev x_is_y = [eqA_eq x y trans c3pf c3p] in
                                hypjoin (list_minf_f ! cmp x (list_minf_f ! cmp y z))
                                        (list_minf_f ! cmp y (list_minf_f ! cmp x z))
                                     by x_is_y end
                          end terminates (eqA x y) by eqA_total
                              join (eqA x y) (eqA x y) ]
                  end terminates (cmp x y) by cmp_total
                      join (cmp x y) (cmp x y) ]
          end terminates (cmp y z'cast) by cmp_total
              join (cmp y z') (cmp y z') ]
    end.

Define list_minf : Fun(A:type)
                      (l:<list A>)
                      (cmp:Fun(x y:A).bool).A :=
  fun(A:type)(l:<list A>)(cmp:Fun(x y:A).bool).
  match (foldr A <option A> (list_minf_f A cmp) (nothing A) l) by fp ft return A with
    nothing A' => abort A
  | something A' a => cast a by symm inj <option *> ft
  end.

Define list_minf_total : Forall(A:type)
                               (l:<list A>)
                               (cmp:Fun(x y:A).bool)
                               (lne:{ l != (nil !) })
                               (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o }).
                         Exists(o:A).
                           { (list_minf ! l cmp) = o } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(cmp:Fun(x y:A).bool)
                                                    (lne:{ l != (nil !) })
                                                    (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o }).
                                              Exists(o:A).
                                                { (list_minf ! l cmp) = o } with
      nil A' =>
        foralli(cmp:Fun(x y:A).bool)
               (lne:{ l != (nil !) }).
          contra trans symm lp
                       lne
            Forall(cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o }).
            Exists(o:A).
              { (list_minf ! l cmp) = o }
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(cmp:Fun(x y:A).bool)
               (lne:{ l != (nil !) })
               (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o }).
          [ induction(f:<option A>) by fp ft IHf return Forall(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                                                        Exists(o:A).
                                                          { (list_minf ! l cmp) = o } with
              nothing A' =>
                foralli(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                  contra trans symm trans fpf fp
                         trans cong (foldr ! ! (list_minf_f ! cmp) (nothing !) *) lp
                         trans join (foldr ! ! (list_minf_f ! cmp) (nothing !) (cons ! h t))
                                    (list_minf_f ! cmp h (foldr ! ! (list_minf_f ! cmp) (nothing !) t))
                               [list_minf_f_is_something A cmp cmp_total hcast terminates (foldr A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total (nothing A) tcast)
                                                                                       by [foldrTot A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total
                                                                                                                 [list_minf_f_total A cmp cmp_total] (nothing A) tcast]]
                    Exists(o:A).
                      { (list_minf ! l cmp) = o }
            | something A' f' =>
                foralli(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                  existsi cast f' by symm inj <option *> ft
                          { (list_minf ! l cmp) = * }
                    hypjoin (list_minf ! l cmp)
                            f'
                         by trans fpf fp end
            end terminates (foldr A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total (nothing A) l)
                        by [foldrTot A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total [list_minf_f_total A cmp cmp_total] (nothing A) l]
                join (foldr ! ! (list_minf_f ! cmp) (nothing !) l)
                     (foldr ! ! (list_minf_f ! cmp) (nothing !) l) ]
    end.

Define msort_preserves_list_minf : Forall(A:type)
                                         (l:<list A>)
                                         (cmp:Fun(x y:A).bool)
                                         (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
                                         (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
                                         (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
                                         (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                         (eqA:Fun(x y:A).bool)
                                         (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
                                         (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
                                         (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y }).
                                     { (list_minf ! l cmp) = (list_minf ! (msort ! l cmp) cmp) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(cmp:Fun(x y:A).bool)
                                                    (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
                                                    (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
                                                    (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
                                                    (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
                                                    (eqA:Fun(x y:A).bool)
                                                    (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
                                                    (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
                                                    (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y }).
                                                { (list_minf ! l cmp) = (list_minf ! (msort ! l cmp) cmp) } with
      nil A' =>
        foralli(cmp:Fun(x y:A).bool)
               (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
               (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
               (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
               (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
               (eqA:Fun(x y:A).bool)
               (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
               (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
               (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y }).
          hypjoin (list_minf ! l cmp)
                  (list_minf ! (msort ! l cmp) cmp)
               by lp end
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        abbrev lne = trans lp
                           clash (cons ! h t)
                                 (nil !) in
        foralli(cmp:Fun(x y:A).bool)
               (cmp_eq:Forall(x y:A)(u:{ (cmp x y) = (cmp y x) }).{ x = y })
               (cmp_inv:Forall(x y:A)(u:{ x != y }).{ (cmp x y) != (cmp y x) })
               (cmp_trans:Forall(x y z:A)(u:{ (cmp x y) = (cmp y z) }).{ (cmp x z) = (cmp x y) })
               (cmp_total:Forall(x y:A).Exists(o:bool).{ (cmp x y) = o })
               (eqA:Fun(x y:A).bool)
               (eqA_total:Forall(x y:A).Exists(o:bool).{ (eqA x y) = o })
               (eqA_eq:Forall(x y:A)(u:{ (eqA x y) = tt }).{ x = y })
               (eqA_neq:Forall(x y:A)(u:{ (eqA x y) = ff }).{ x != y }).
          abbrev list_minf_f_strong_comm = foralli(x:A)(b:<option A>)(l1 l2:<list A>).[strengthen_comm A <option A>
                                                                                                       x l1 l2
                                                                                                       terminates (list_minf_f A cmp) by list_minf_f_partapp_total
                                                                                                       b
                                                                                                       foralli(b:<option A>)(x1 x2:A).[list_minf_f_comm A cmp cmp_eq cmp_inv cmp_trans cmp_total eqA eqA_total eqA_eq eqA_neq x2 x1 b]
                                                                                                       [list_minf_f_total A cmp cmp_total]] in
          [ induction(f:<option A>) by fp ft IHf return Forall(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                                                          { (list_minf ! l cmp) = (list_minf ! (msort ! l cmp) cmp) } with
              nothing A' =>
                foralli(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                  contra trans symm trans fpf fp
                         trans cong (foldr ! ! (list_minf_f ! cmp) (nothing !) *) lp
                         trans join (foldr ! ! (list_minf_f ! cmp) (nothing !) (cons ! h t))
                                    (list_minf_f ! cmp h (foldr ! ! (list_minf_f ! cmp) (nothing !) t))
                               [list_minf_f_is_something A cmp cmp_total hcast terminates (foldr A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total (nothing A) tcast)
                                                                                       by [foldrTot A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total
                                                                                                                 [list_minf_f_total A cmp cmp_total] (nothing A) tcast]]
                    { (list_minf ! l cmp) = (list_minf ! (msort ! l cmp) cmp) }
            | something A' f' =>
                foralli(fpf:{ (foldr ! ! (list_minf_f ! cmp) (nothing !) l) = f }).
                  hypjoin (list_minf ! l cmp)
                          (list_minf ! (msort ! l cmp) cmp)
                       by trans fpf fp
                          symm trans symm [foldr_pf2 A <option A>
                                                     terminates (list_minf_f A cmp) by list_minf_f_partapp_total
                                                     l (nothing A) list_minf_f_strong_comm [list_minf_f_total A cmp cmp_total] cmp cmp_total]
                               trans fpf fp end
            end terminates (foldr A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total (nothing A) l)
                        by [foldrTot A <option A> terminates (list_minf_f A cmp) by list_minf_f_partapp_total
                                                  [list_minf_f_total A cmp cmp_total] (nothing A) l]
                join (foldr ! ! (list_minf_f ! cmp) (nothing !) l)
                     (foldr ! ! (list_minf_f ! cmp) (nothing !) l) ]
    end.
