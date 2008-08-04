Include "nat.g".

%Set "print_parsed".

Inductive list : Fun(A:type).type :=
  nil : Fun(A:type).<list A>
| cons : Fun(A:type)(a:A)(l:<list A>). <list A>.

Define isnil := fun(A:type)(owned l:<list A>). 
                  match l with nil A' => tt | cons A' a' l' => ff end.

Set "refine_cases".

Define foldr : Fun(A B C: type)(owned cookie:C)
                  (fcn: Fun(owned cookie:C)(owned x:A)(y:B).B)
                  (b:B)(owned l : <list A>).B :=
  fun foldr(A B C: type)(owned cookie:C)
           (fcn: Fun(owned cookie:C)(owned x:A)(y:B).B)
           (b:B)(owned l : <list A>):B.
    match l with
      nil A' => b
   | cons A' a' l' => (fcn cookie a' 
                         (foldr A B C cookie fcn b l'))
   end. 

Unset "refine_cases".

Define foldrTot : Forall(A B C : type)
                        (cookie:C)(f:Fun(cookie:C)(x:A)(y:B).B)
                        (fTot:Forall(x:A)(y:B).Exists(z:B).
                                 {(f cookie x y) = z})
                        (b:B)(l:<list A>).
                        Exists(z:B). {(foldr cookie f b l) = z } :=
  foralli(A B C : type)(cookie:C)(f:Fun(cookie:C)(x:A)(y:B).B)
         (fTot:Forall(x:A)(y:B).Exists(z:B).{(f cookie x y) = z})(b:B).
    induction(l:<list A>) by u v IH 
      return Exists(z:B). {(foldr cookie f b l) = z } with
        nil A' => existsi b {(foldr cookie f b l) = *}
                   hypjoin (foldr cookie f b l) b by u end
      | cons A' a' l' => existse [IH cast l' by symm v]
                         foralli(z:B)(u1:{(foldr cookie f b l') = z}).
                           existse [fTot cast a' by symm inj <list *> v z]
                           foralli(z':B)(u2:{(f cookie a' z) = z'}).
                             existsi z' {(foldr cookie f b l) = *}
                               trans hypjoin 
                                       (foldr cookie f b l)
                                       (f cookie a' (foldr cookie f b l'))
                                      by u end
                               trans cong (f cookie a' *) u1
                                     u2
      end.

Inductive map_i : Fun(A B:type).type :=
  mk_map_i : Fun(A B C:type)
                (fcn:Fun(owned cookie:C)(owned a:A).B)
                (cookie:C).<map_i A B>.

Define map_h :=
  fun(spec A B:type)(owned Fcookie:<map_i A B>)(owned a:A)(l': <list B>).
    match Fcookie with
      mk_map_i A' B' C fcn cookie =>
        abbrev PA = inj <map_i * **> Fcookie_Eq in
        abbrev PB' = symm inj <map_i ** *> Fcookie_Eq in
        abbrev PlistB' = cong <list *> PB' in
          cast (cons B' (fcn cookie cast a by PA) cast l' by symm PlistB')
          by PlistB'
    end.

Define map : Fun(A B C: type)(owned cookie:C)
                (fcn: Fun(owned cookie:C)(owned a:A).B)
                (owned l : <list A>).<list B> :=
  fun(A B C: type)(owned cookie:C)
     (fcn: Fun(owned cookie:C)(owned a:A).B)
     (owned l : <list A>): <list B>.
    let Fcookie = (mk_map_i A B C fcn inc cookie) in
    let ret = 
     (foldr A <list B> <map_i A B> Fcookie (map_h A B) (nil B) l) 
    in dec Fcookie ret.

Define map_total : Forall(A B C: type)(cookie:C)
                         (fcn: Fun(cookie:C)(a:A).B)
                         (fcnTot:Forall(a:A).Exists(b:B).{(fcn cookie a) = b})
                         (l1 : <list A>).
                         Exists(l2:<list B>).
                           { (map cookie fcn l1) = l2 } :=
  foralli(A B C: type)(cookie:C)
         (fcn: Fun(cookie:C)(a:A).B)
         (fcnTot:Forall(a:A).Exists(b:B).{(fcn cookie a) = b})
         (l1 : <list A>).
  abbrev Fcookie = (mk_map_i A B C fcn cookie) in
  existse
   [foldrTot A <list B> <map_i A B> Fcookie (map_h A B) 
      foralli(a:A)(l:<list B>).
        existsi (cons B terminates (fcn cookie a) by [fcnTot a] l)
          { (map_h Fcookie a l) = * }
          join (map_h Fcookie a l) (cons (fcn cookie a) l)
       (nil B) l1]
  foralli(z:<list B>)(uz:{(foldr Fcookie map_h nil l1) = z}).
  existsi z { (map cookie fcn l1) = * }
    trans join (map cookie fcn l1) (foldr Fcookie map_h nil l1)
          uz.

Inductive append_i : Fun(A:type).type :=
  mk_append_i : Fun(A:type).<append_i A>.

Define append_h := 
  fun(spec A:type)(owned cookie:<append_i A>)(owned x:A)(l:<list A>).
    match cookie with
      mk_append_i A' => 
       abbrev P = inj <append_i *> cookie_Eq in
         cast (cons A' inc cast x by P cast l by cong <list *> P) 
         by cong <list *> symm P
    end.

Define append : Fun(A : type)(owned l1:<list A>)(l2: <list A>).<list A> :=
  fun(A : type)(owned l1:<list A>)(l2: <list A>) : <list A>.
  let cookie = (mk_append_i A) in
  let ret = 
      (foldr A <list A> <append_i A> cookie (append_h A)
        l2 l1) in
    dec cookie ret.

Define appendTot : Forall(A : type)(l1 l2: <list A>).Exists(l : <list A>).
                      { (append A l1 l2) = l } :=
  foralli(A : type)(l1 l2: <list A>).
  abbrev cookie = (mk_append_i A) in
  existse [foldrTot A <list A> <append_i A> cookie
             (append_h A)
             foralli(x:A)(l:<list A>).
               existsi (cons A x l) { (append_h cookie x l) = * }
                 join (append_h cookie x l) (cons x l)
             l2 l1] 
  foralli(z:<list A>)(u:{(foldr cookie append_h l2 l1) = z}).
    existsi z {(append l1 l2) = *}
      trans join (append l1 l2) 
                 (foldr cookie append_h l2 l1)
            u.

Define foldr_append
  : Forall(A B C : type)(cookie:C)
          (f:Fun(cookie:C)(a:A)(b:B).B)(b:B)
          (l1 l2:<list A>).
     {(foldr cookie f b (append l1 l2)) =
        (foldr cookie f (foldr cookie f b l2) l1)} :=
  foralli(A B C : type)(cookie:C)
         (f:Fun(cookie:C)(a:A)(b:B).B)(b:B).
    induction(l1:<list A>) by u v IH 
    return Forall(l2:<list A>).
           {(foldr cookie f b (append l1 l2)) = 
              (foldr cookie f (foldr cookie f b l2) l1)} with
      nil A' => foralli(l2:<list A>).
                  trans cong (foldr cookie f b (append * l2)) u
                  trans join (foldr cookie f b (append nil l2))
                             (foldr cookie f (foldr cookie f b l2) nil)
                        cong (foldr cookie f (foldr cookie f b l2) *) symm u
   | cons A' a' l1' => 
       foralli(l2:<list A>).
        trans cong (foldr cookie f b (append * l2)) u
        trans join (foldr cookie f b (append (cons a' l1') l2))
                   (f cookie a' (foldr cookie f b (append l1' l2)))
        trans cong (f cookie a' *) [IH cast l1' by symm v l2]
        trans join (f cookie a' (foldr cookie f (foldr cookie f b l2) l1'))
                   (foldr cookie f (foldr cookie f b l2) (cons a' l1'))
              cong (foldr cookie f (foldr cookie f b l2) *) symm u
   end.

Define append_assoc
 : Forall(A:type)(l1 l2 l3:<list A>).
     { (append (append l1 l2) l3) = (append l1 (append l2 l3)) } :=
  foralli(A:type)(l1 l2 l3:<list A>).
    trans join (append (append l1 l2) l3)
               (foldr mk_append_i append_h l3 (append l1 l2))
    trans [foldr_append A <list A> <append_i A> (mk_append_i A)
            (append_h A) l3 l1 l2]
          join (foldr mk_append_i append_h
                  (foldr mk_append_i append_h l3 l2) l1)
               (append l1 (append l2 l3)).

Define map_append : 
  Forall(A B C:type)(cookie:C)(fcn: Fun(cookie:C)(a:A).B)
        (l1 l2:<list A>).
    { (map cookie fcn (append l1 l2)) = 
      (append (map cookie fcn l1) (map cookie fcn l2)) } :=
  foralli(A B C:type)(cookie:C)(fcn: Fun(cookie:C)(a:A).B)
         (l1 l2:<list A>).
  abbrev f = (map_h A B) in
  abbrev Fcookie = (mk_map_i A B C fcn cookie) in
     trans join (map cookie fcn (append l1 l2))
                (foldr Fcookie f nil (append l1 l2))
     trans [foldr_append A <list B> <map_i A B> Fcookie f (nil B) l1 l2]
     trans join (foldr Fcookie f (foldr Fcookie f nil l2) l1) 
                (foldr Fcookie f (map cookie fcn l2) l1)
     abbrev L2 = (map cookie fcn l2) in
     trans [induction(l1:<list A>) 
              return { (foldr Fcookie f L2 l1) =
                          (append (foldr Fcookie f nil l1) L2) }
              with
              nil A' => hypjoin
                          (foldr Fcookie f L2 l1)
                          (append (foldr Fcookie f nil l1) L2)
                        by l1_eq end
            | cons A' a' l1' => 
              hypjoin
                (foldr Fcookie f L2 l1)
                (append (foldr Fcookie f nil l1) L2)
              by l1_eq [l1_IH cast l1' by symm l1_Eq ] end
            end
           l1]
      cong (append * L2) join (foldr Fcookie f nil l1) (map cookie fcn l1).

Define append_nil : Forall(A:type)(l:<list A>).{ (append l nil) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (append l nil) = l } with
      nil A' =>
        hypjoin (append l nil)
                l
             by lp end
    | cons A' h t =>
        trans hypjoin (append l nil)
                      (cons h (append t nil))
                   by lp end
        trans cong (cons h *)
                   [IHl cast t by cong <list *> symm inj <list *> lt]
              symm lp
    end.

Define eqlist : Fun(A:type)(eqA:Fun(owned x1 x2:A).bool)
                   (owned l1 l2:<list A>)
                   .bool :=
  fun eqlist(A:type)(eqA:Fun(owned x1 x2:A).bool)(owned l1 l2:<list A>):bool.
  match l1 by l1p l1t return bool with
    nil A1 =>
      match l2 by l2p l2t return bool with
        nil A2 => tt
      | cons A2 h2 t2 => ff
      end
  | cons A1 h1 t1 =>
      match l2 by l2p l2t return bool with
        nil A2 =>
          ff
      | cons A2 h2 t2 =>
          abbrev h1cast = cast h1 by symm inj <list *> l1t in
          abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
          abbrev h2cast = cast h2 by symm inj <list *> l2t in
          abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
          (and (eqA h1cast h2cast) (eqlist A eqA t1cast t2cast))
      end
  end.

Define eqlist_total
 : Forall(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
         (l1 l2:<list A>).
      Exists(o:bool).{ (eqlist eqA l1 l2) = o } :=
  foralli(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
    induction(l1:<list A>) by l1p l1t IHl1 
    return Forall(l2:<list A>).Exists(o:bool).{ (eqlist eqA l1 l2) = o } with
      nil A1 =>
        foralli(l2:<list A>).
          case l2 by l2p l2t with
          nil A2 =>
              existsi tt
                      { (eqlist eqA l1 l2) = * }
                hypjoin (eqlist eqA l1 l2)
                        tt
                     by l1p
                        l2p end
        | cons A2 h2 t2 =>
              existsi ff
                      { (eqlist eqA l1 l2) = * }
                hypjoin (eqlist eqA l1 l2)
                        ff
                     by l1p
                        l2p end
        end
    | cons A1 h1 t1 =>
        foralli(l2:<list A>).
        case l2 by l2p l2t with
          nil A2 =>
              existsi ff
                      { (eqlist eqA l1 l2) = * }
                hypjoin (eqlist eqA l1 l2)
                        ff
                     by l1p
                        l2p end
        | cons A2 h2 t2 =>
              abbrev h1cast = cast h1 by symm inj <list *> l1t in
              abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
              abbrev h2cast = cast h2 by symm inj <list *> l2t in
              abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
              existse [IHl1 t1cast t2cast]
                foralli(o2:bool)(o2pf:{ (eqlist eqA t1 t2) = o2 }).
                  existse [and_total terminates (eqA h1cast h2cast) by eqA_total o2]
                    foralli(o:bool)(opf:{ (and (eqA h1 h2) o2) = o }).
                      existsi o
                              { (eqlist eqA l1 l2) = * }
                        trans hypjoin (eqlist eqA l1 l2)
                                      (and (eqA h1 h2) o2)
                                   by l1p
                                      l2p
                                      symm o2pf end
                              opf
        end
    end.

Define eqlistEq : Forall(A:type)
                        (l1 l2:<list A>)
                        (eqA:Fun(x1 x2:A).bool)
                        (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                        (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                        (u:{ (eqlist eqA l1 l2) = tt }).
                    { l1 = l2 } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)
                                                        (eqA:Fun(x1 x2:A).bool)
                                                        (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                                                        (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                                                        (u:{ (eqlist eqA l1 l2) = tt }).
                                                    { l1 = l2 } with
      nil A1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(eqA:Fun(x1 x2:A).bool)
                                                            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                                                            (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                                                            (u:{ (eqlist eqA l1 l2) = tt }).
                                                        { l1 = l2 } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist eqA l1 l2) = tt }).
              hypjoin l1 l2 by l1p l2p end
        | cons A2 h2 t2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist eqA l1 l2) = tt }).
              contra trans hypjoin ff
                                   (eqlist eqA l1 l2)
                                by l1p
                                   l2p end
                     trans u
                           clash tt ff
                { l1 = l2 }
        end
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(eqA:Fun(x1 x2:A).bool)
                                                            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                                                            (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                                                            (u:{ (eqlist eqA l1 l2) = tt }).
                                                        { l1 = l2 } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist eqA l1 l2) = tt }).
              contra trans hypjoin ff
                                   (eqlist eqA l1 l2)
                                by l1p
                                   l2p end
                     trans u
                           clash tt ff
                { l1 = l2 }
        | cons A2 h2 t2 =>
            abbrev h1cast = cast h1 by symm inj <list *> l1t in
            abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
            abbrev h2cast = cast h2 by symm inj <list *> l2t in
            abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist eqA l1 l2) = tt }).
              existse [eqlist_total A eqA eqA_total t1cast t2cast]
                foralli(o2:bool)(o2pf:{ (eqlist eqA t1 t2) = o2 }).
                  abbrev eqlist_is_and_eqA_o2 =
                                                      symm trans symm u
                                                                 hypjoin (eqlist eqA l1 l2)
                                                                         (and (eqA h1 h2) o2)
                                                                      by l1p
                                                                         l2p
                                                                         o2pf end in
                  abbrev u' = symm trans symm [andtt_e2 terminates (eqA h1cast h2cast) by eqA_total
                                                        o2
                                                        eqlist_is_and_eqA_o2]
                                         symm o2pf in
                  abbrev taileq = [IHl1 t1cast t2cast eqA eqA_total eqA_eq u'] in
                  abbrev andtt = symm trans symm u
                                            hypjoin (eqlist eqA l1 l2)
                                                    (and (eqA h1 h2) (eqlist eqA t1 t2))
                                                 by l1p
                                                    l2p
                                                    taileq end in
                  abbrev eqAeq = [eqA_eq h1cast h2cast [andtt_e1 terminates (eqA h1cast h2cast) by eqA_total
                                                                 o2
                                                                 eqlist_is_and_eqA_o2]] in
                  trans l1p
                  trans cong (cons * t1) eqAeq
                  trans cong (cons h2 *) taileq
                        symm l2p
        end
    end.

Define member : Fun(A:type)
                   (owned x:A)
                   (owned l:<list A>)
                   (eqA:Fun(owned x1 x2:A).bool).bool :=
  fun member(A:type)
            (owned x:A)
            (owned l:<list A>)
            (eqA:Fun(owned x1 x2:A).bool):bool.
  match l by lp lt return bool with
    nil A' =>
      ff
  | cons A' h t =>
      abbrev hcast = cast h by symm inj <list *> lt in
      abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
      (or (eqA x hcast) (member A x tcast eqA))
  end.

Define member_total : Forall(A:type)
                            (x:A)
                            (l:<list A>)
                            (eqA:Fun(x1 x2:A).bool)
                            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
                      Exists(z:bool).
                        { (member ! x l eqA) = z } :=
  foralli(A:type)
         (x:A).
    induction(l:<list A>) by lp lt IHl return Forall(eqA:Fun(x1 x2:A).bool)
                                                    (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
                                              Exists(z:bool).
                                                { (member ! x l eqA) = z } with
      nil A' =>
        foralli(eqA:Fun(x1 x2:A).bool)
               (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
          existsi ff
                  { (member ! x l eqA) = * }
            hypjoin (member ! x l eqA)
                    ff
                 by lp end
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(eqA:Fun(x1 x2:A).bool)
               (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
          existse [IHl tcast eqA eqA_total]
            foralli(zr:bool)(zrpf:{ (member x t eqA) = zr }).
              existse [or_total terminates (eqA x hcast) by eqA_total zr]
                foralli(z:bool)(zpf:{ (or (eqA x h) zr) = z }).
                  existsi z
                          { (member x l eqA) = * }
                    trans cong (member x * eqA) lp
                    trans join (member x (cons h t) eqA)
                               (or (eqA x h) (member x t eqA))
                    trans cong (or (eqA x h) *) zrpf
                          zpf
    end.

Define all : Fun(A C:type)(owned c:C)
                (f:Fun(owned c:C)(owned a:A).bool)(owned l:<list A>).bool :=
  fun(A C:type)(owned c:C)(f:Fun(owned c:C)(owned a:A).bool).
    (foldr A bool C c fun(owned c:C)(owned a:A)(b:bool).(and (f c a) b) tt).