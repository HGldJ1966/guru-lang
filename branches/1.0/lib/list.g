%Set "show_includes".

Include "plus.g".

Inductive list : Fun(A:type).type :=
  nil : Fun(A:type).<list A>
| cons : Fun(A:type)(a:A)(l:<list A>). <list A>.

Define isnil := fun(A:type)(^#owned l:<list A>). 
                  match l with nil A' => tt | cons A' a' l' => ff end.

Define foldr : Fun(A B C: type)(^#owned cookie:C)
                  (fcn: Fun(^#owned cookie:C)(^#owned x:A)(y:B).B)
                  (b:B)(^#owned l : <list A>).B :=
  fun foldr(A B C: type)(^#owned cookie:C)
           (fcn: Fun(^#owned cookie:C)(^#owned x:A)(y:B).B)
           (b:B)(^#owned l : <list A>):B.
    match l with
      nil _ => b
   | cons _ a' l' => (fcn cookie a' 
                         (foldr A B C (clone_owned C cookie) fcn b l'))
   end. 

Define spec foldr1 : Fun(A B:type)(f:Fun(a:A)(y:B).B)(b:B)(l:<list A>).B :=
  fun foldr1(A B:type)(f:Fun(a:A)(y:B).B)(b:B)(l:<list A>):B.
    (foldr A B nat Z fun(u:nat)(x:A)(y:B).(f x y) b l).

Define foldl' : Fun(A B: type) (fcn : Fun (x : A) (y : B) . B) (b : B)
  (l : <list A>) . B :=
  fun foldl (A B : type) (fcn : Fun (x : A) (y : B) . B) (b : B)
    (l : <list A>) : B .
    match l with
        nil _ => b
      | cons _ a' l' => (foldl A B fcn (fcn a' b) l')
  end.

Define foldl : Fun(A B C: type)(^#owned cookie:C)
                   (fcn : Fun(^#owned cookie:C)(^#owned x : A)(y : B) . B)
                   (b : B)(^#owned l : <list A>) . B :=
  fun foldl (A B C: type)(^#owned cookie:C)
            (fcn : Fun(^#owned cookie:C)(^#owned x : A)(y : B). B)
            (b : B)(^#owned l : <list A>) : B .
    match l with
        nil _ => b
      | cons _ a' l' => (foldl A B C (clone_owned C cookie) fcn (fcn cookie a' b) l')
  end.

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
      | cons _ a' l' => existse [IH l']
                         foralli(z:B)(u1:{(foldr cookie f b l') = z}).
                           existse [fTot a' z]
                           foralli(z':B)(u2:{(f cookie a' z) = z'}).
                             existsi z' {(foldr cookie f b l) = *}
                               trans hypjoin 
                                       (foldr cookie f b l)
                                       (f cookie a' (foldr cookie f b l'))
                                      by u end
                               trans cong (f cookie a' *) u1
                                     u2
      end.

Define foldr1Tot :=
  foralli(A B : type)(f:Fun(x:A)(y:B).B)
         (fTot:Forall(x:A)(y:B).Exists(z:B).{(f x y) = z})(b:B)(l:<list A>).
    existsi terminates (foldr A B nat Z fun(u:nat)(x:A)(y:B).(f x y) b l) by
            [foldrTot A B nat Z fun(u:nat)(x:A)(y:B).(f x y) 
               foralli(x:A)(y:B). existsi terminates (f x y) by [fTot x y]
                                    { (fun(u:nat)(x:A)(y:B).(f x y) Z x y) = *}
                                  join (fun(u:nat)(x:A)(y:B).(f x y) Z x y) (f x y)
               b l]
       { (foldr1 f b l) = * }
       join (foldr1 f b l) (foldr Z fun(u)(x)(y).(f x y) b l).

Define foldr_ext : Forall(A B C : type)
                         (cookie1 cookie2:C)(f1 f2:Fun(cookie:C)(x:A)(y:B).B)
                         (f1Tot:Forall(x:A)(y:B).Exists(z:B). {(f1 cookie1 x y) = z})
                         (feq:Forall(x:A)(y:B).
                                  {(f1 cookie1 x y) = (f2 cookie2 x y)})
                         (b:B)(l:<list A>).
                    { (foldr cookie1 f1 b l) = (foldr cookie2 f2 b l) } :=
  foralli(A B C : type)
         (cookie1 cookie2:C)(f1 f2:Fun(cookie:C)(x:A)(y:B).B)
         (f1Tot:Forall(x:A)(y:B).Exists(z:B). {(f1 cookie1 x y) = z})
         (feq:Forall(x:A)(y:B).
               {(f1 cookie1 x y) = (f2 cookie2 x y)})
         (b:B).
  induction(l:<list A>) return { (foldr cookie1 f1 b l) = (foldr cookie2 f2 b l) } 
  with
    nil _ => hypjoin (foldr cookie1 f1 b l) (foldr cookie2 f2 b l) by l_eq end
  | cons _ a l' => hypjoin (foldr cookie1 f1 b l) (foldr cookie2 f2 b l) 
                   by l_eq [l_IH l'] 
                      [feq a terminates (foldr A B C cookie1 f1 b l')
                             by [foldrTot A B C cookie1 f1 f1Tot b l']] end
  end.

Inductive map_i : Fun(A B:type).type :=
  mk_map_i : Fun(A B C:type)
                (fcn:Fun(^#owned cookie:C)(^#owned a:A).B)
                (cookie:C).<map_i A B>.

Define map_h :=
  fun(spec A B:type)(^#owned Fcookie:<map_i A B>)(^#owned a:A)(l': <list B>).
    match Fcookie with
      mk_map_i A' B' C fcn cookie =>
        abbrev PA = inj <map_i * **> Fcookie_Eq in
        abbrev PB' = symm inj <map_i ** *> Fcookie_Eq in
        abbrev PlistB' = cong <list *> PB' in
          cast (cons B' (fcn cookie cast a by PA) cast l' by symm PlistB')
          by PlistB'
    end.

Define map : Fun(A B C: type)(^#owned cookie:C)
                (fcn: Fun(^#owned cookie:C)(^#owned a:A).B)
                (^#owned l : <list A>).<list B> :=
  fun(A B C: type)(^#owned cookie:C)
     (fcn: Fun(^#owned cookie:C)(^#owned a:A).B)
     (^#owned l : <list A>): <list B>.
    let Fcookie = (mk_map_i A B C fcn (inc C cookie)) in
    let ret = 
     (foldr A <list B> <map_i A B> Fcookie (map_h A B) (nil B) l) 
    in 
   do (dec <map_i A B> Fcookie)
      ret
   end.

Define spec map1 : Fun(A B:type)(f:Fun(a:A).B)(l:<list A>).<list B> :=
  fun map1(A B:type)(f:Fun(a:A).B)(l:<list A>):<list B>.
    (map A B nat Z fun(u:nat)(a:A).(f a) l).

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

Define map_ext : Forall(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
                       (fTot : Forall(a:A). Exists(b:B). { (f1 cookie1 a) = b })
                       (feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
                       (l:<list A>).
                  { (map cookie1 f1 l) = (map cookie2 f2 l) } :=
  foralli(A B C:type)(f1 f2:Fun(c:C)(a:A).B)(cookie1 cookie2:C)
         (fTot : Forall(a:A). Exists(b:B). { (f1 cookie1 a) = b })
         (feq : Forall(a:A). {(f1 cookie1 a) = (f2 cookie2 a)})
         (l:<list A>).
    transs join (map cookie1 f1 l) (foldr (mk_map_i f1 cookie1) map_h nil l)
           [foldr_ext A <list B> <map_i A B> (mk_map_i A B C f1 cookie1)
             (mk_map_i A B C f2 cookie2) (map_h A B) (map_h A B)
             foralli(x:A)(y:<list B>). 
               existsi (cons B terminates (f1 cookie1 x) by fTot y)
                 { (map_h (mk_map_i f1 cookie1) x y) = *}
                 join (map_h (mk_map_i f1 cookie1) x y) (cons (f1 cookie1 x) y)
             foralli(x:A)(y:<list B>). 
               hypjoin (map_h (mk_map_i f1 cookie1) x y) (map_h (mk_map_i f2 cookie2) x y) 
               by [feq x] end
             (nil B) l]
           join (foldr (mk_map_i f2 cookie2) map_h nil l) (map cookie2 f2 l)
    end.

Define map1_total : Forall(A B: type)
                          (fcn: Fun(a:A).B)
                          (fcnTot:Forall(a:A).Exists(b:B).{(fcn a) = b})
                          (l1 : <list A>).
                          Exists(l2:<list B>).
                            { (map1 fcn l1) = l2 } :=
  foralli(A B: type)
         (fcn: Fun(a:A).B)
         (fcnTot:Forall(a:A).Exists(b:B).{(fcn a) = b})
         (l1 : <list A>).
   existsi terminates (map A B nat Z fun(u:nat)(a:A).(fcn a) l1) by
             [map_total A B nat Z fun(u:nat)(a:A).(fcn a)
                foralli(a:A).existsi terminates (fcn a) by fcnTot
                                { (fun(u)(a).(fcn a) Z a) = *} 
                                join (fun(u)(a).(fcn a) Z a) (fcn a)
                l1]
      {(map1 fcn l1) = *}
      join (map1 fcn l1) (map Z fun(u)(a).(fcn a) l1).

Define map1_ext : Forall(A B:type)(f1 f2:Fun(a:A).B)
                        (fTot : Forall(a:A). Exists(b:B). { (f1 a) = b })
                        (feq : Forall(a:A). {(f1 a) = (f2 a)})
                        (l:<list A>).
                   { (map1 f1 l) = (map1 f2 l) } :=
   foralli(A B:type)(f1 f2:Fun(a:A).B)
          (fTot : Forall(a:A). Exists(b:B). { (f1 a) = b })
          (feq : Forall(a:A). {(f1 a) = (f2 a)})
          (l:<list A>).
   transs join (map1 f1 l) (map Z fun(u)(a).(f1 a) l)
          [map_ext A B nat fun(u:nat)(a:A).(f1 a) 
             fun(u:nat)(a:A).(f2 a) 
             Z Z
             foralli(x:A).existsi terminates (f1 x) by fTot
                            { (fun(u)(a).(f1 a) Z x) = *} 
                            join (fun(u)(a).(f1 a) Z x) (f1 x)
             foralli(x:A). hypjoin (fun(u)(a).(f1 a) Z x) (fun(u)(a).(f2 a) Z x)
                           by [feq x] end
             l]
         join (map Z fun(u)(a).(f2 a) l) (map1 f2 l)
   end.

Define nth : Fun(A:type)(n:nat)(l:<list A>).A :=
  fun nth(A:type)(n:nat)(l:<list A>):A.
    match l with
      nil _ => abort A
    | cons _ a l' =>
      match n with
        Z => a
      | S n' => (nth A n' l')
      end
    end.

Define set_nth : Fun(A:type)(n:nat)(l:<list A>)(b:A).<list A> :=
  fun set_nth(A:type)(n:nat)(l:<list A>)(b:A):<list A>.
    match l with
      nil _ => abort <list A>
    | cons _ a l' =>
      match n with
        Z => (cons A b l')
      | S n' => (cons A a (set_nth A n' l' b))
      end
    end.

Define set_nth_other : Forall(A:type)(l:<list A>)(n m:nat)(b:A)
                             (u:{ n != m }).
                        { (nth n (set_nth m l b)) = (nth n l) } :=
  foralli(A:type).
  induction(l:<list A>) 
  return Forall(n m:nat)(b:A)
               (u:{ n != m }).
          { (nth n (set_nth m l b)) = (nth n l) } with
    nil _ =>
    foralli(n m:nat)(b:A)(u:{ n != m }).
      hypjoin (nth n (set_nth m l b)) (nth n l) by l_eq end
  | cons _ a l' =>
    foralli(n m:nat)(b:A)(u:{ n != m }). 
      case m with
        Z =>     
          case n with
            Z => contra trans m_eq
                              trans symm n_eq u
                   { (nth n (set_nth m l b)) = (nth n l) }
          | S n' => 
              hypjoin (nth n (set_nth m l b)) (nth n l)
                by l_eq m_eq n_eq end
          end
      | S m' => 
          case n with
            Z => hypjoin (nth n (set_nth m l b)) (nth n l)
                   by l_eq m_eq n_eq end
          | S n' => 
            hypjoin (nth n (set_nth m l b)) (nth n l)
              by l_eq m_eq n_eq 
                 [l_IH l' n' m' b 
                    diseqi foralli(u1:{n' = m'}).
                           contra
                             transs cong (S *) u1
                                    symm m_eq
                                    symm trans symm n_eq u 
                             end
                           False]
              end
          end
      end
  end.

Define filter :=
  fun filter(A C:type)(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool)
            (^#owned l:<list A>) : <list A> .
    match l with
       nil _ => (nil A)
    | cons _ a l' => match (f c a) with 
                       ff => (filter A C c f l')
                     | tt => (cons A a (filter A C c f l'))
                     end
    end.

Define filter_total :=
  foralli(A C:type)
         (c:C)
         (f:Fun(c:C)(a:A).bool)
         (f_total:Forall(c:C)(a:A).Exists(z:bool).{(f c a) = z}).
  induction(l:<list A>) return Exists(l2:<list A>).{ (filter c f l) = l2 }
  with
    nil _ => existsi (nil A) { (filter c f l) = * }
               hypjoin (filter c f l) nil by l_eq end
  | cons _ a l' =>
      existse [l_IH l']
      foralli(l2':<list A>)(l2'_pf:{ (filter c f l') = l2' }).
      existse [f_total c a]
      foralli(z:bool)(z_pf:{ (f c a) = z }).
      case z with
        ff =>
          existsi l2' { (filter c f l) = * }
            hypjoin (filter c f l) l2' by l_eq l2'_pf z_pf z_eq end
      | tt =>
          existsi (cons A a l2') { (filter c f l) = * }
            hypjoin (filter c f l) (cons a l2') by l_eq l2'_pf z_pf z_eq end
      end
  end.


Inductive append_i : Fun(A:type).type :=
  mk_append_i : Fun(A:type).<append_i A>.

Define append_h := 
  fun(spec A:type)(^#owned cookie:<append_i A>)(^#owned x:A)(l:<list A>).
    match cookie with
      mk_append_i A' => 
       abbrev P = inj <append_i *> cookie_Eq in
       cast
         (cons A' (inc_owned A' x) l)
       by cong <list *> symm P
    end.

Define append : Fun(A : type)(^#owned l1:<list A>)(l2: <list A>).<list A> :=
  fun(A : type)(^#owned l1:<list A>)(l2: <list A>) : <list A>.
  let cookie = (mk_append_i A) in
  let ret = 
      (foldr A <list A> <append_i A> (inspect <append_i A> cookie) (append_h A)
        l2 l1) in
    do (dec <append_i A> cookie)
       ret
    end.

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

Total append appendTot.

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

Define foldr1_append
  : Forall(A B : type)
          (f:Fun(a:A)(b:B).B)(b:B)
          (l1 l2:<list A>).
     {(foldr1 f b (append l1 l2)) =
        (foldr1 f (foldr1 f b l2) l1)} :=
   foralli(A B : type)
          (f:Fun(a:A)(b:B).B)(b:B)
          (l1 l2:<list A>).
     transs join (foldr1 f b (append l1 l2))
                 (foldr Z fun(u)(x)(y).(f x y) b (append l1 l2))
            [foldr_append A B nat Z fun(x:nat)(a:A)(b:B).(f a b) b l1 l2]
            join (foldr Z fun(x:nat)(a:A)(b:B).(f a b) (foldr Z  fun(x:nat)(a:A)(b:B).(f a b) b l2) l1)
                 (foldr1 f (foldr1 f b l2) l1)
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

Define map1_append : 
   Forall(A B:type)(f: Fun(a:A).B)(l1 l2:<list A>).
     { (map1 f (append l1 l2)) = (append (map1 f l1) (map1 f l2)) } :=
   foralli(A B:type)(f: Fun(a:A).B)(l1 l2:<list A>).
   transs join (map1 f (append l1 l2)) (map Z fun(u:nat)(a:A).(f a) (append l1 l2))
          [map_append A B nat Z fun(u:nat)(a:A).(f a) l1 l2]
          join (append (map Z fun(u:nat)(a:A).(f a) l1) (map Z fun(u:nat)(a:A).(f a) l2))
               (append (map1 f l1) (map1 f l2))
   end.


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

Define spec concat : Fun(A:type)(l:<list <list A>>).<list A> :=
  fun(A:type)(l:<list <list A>>).
    (foldr1 <list A> <list A> (append A) (nil A) l).

Define concat_tot :=
  foralli(A:type)(l:<list <list A>>).
    existsi terminates (foldr1 <list A> <list A> (append A) (nil A) l) by
              [foldr1Tot <list A> <list A> (append A) [appendTot A] (nil A) l]
      { (concat l) = *}
      join (concat l) (foldr1 append nil l).

Total concat concat_tot.

Define map1_concat : Forall(A B:type)(f:Fun(x:A).B)(l:<list <list A>>).
                       { (map1 f (concat l)) = (concat (map1 fun(x).(map1 f x) l)) } :=
  foralli(A B:type)(f:Fun(x:A).B).
    induction(l:<list <list A>>) return { (map1 f (concat l)) = (concat (map1 fun(x).(map1 f x) l)) }
    with
      nil _ => hypjoin (map1 f (concat l)) (concat (map1 fun(x).(map1 f x) l)) by l_eq end
    | cons _ x l' => 
      transs hypjoin (map1 f (concat l)) (map1 f (append x (concat l'))) by l_eq end
             [map1_append A B f x (concat A l')]
             cong (append (map1 f x) *) [l_IH l']
             hypjoin (append (map1 f x) (concat (map1 fun(x).(map1 f x) l')))  
                     (concat (map1 fun(x).(map1 f x) l)) 
               by l_eq end
      end
    end.
        
Define concat_append : Forall(A:type)(l1 l2:<list <list A>>).
                         { (concat (append l1 l2)) = (append (concat l1) (concat l2)) } :=
 foralli(A:type)(l1 l2:<list <list A>>).
   transs join (concat (append l1 l2))
               (foldr1 append nil (append l1 l2))
          [foldr1_append <list A> <list A> (append A) (nil A) l1 l2]
          join (foldr1 append (foldr1 append nil l2) l1)
               (foldr1 append (concat l2) l1)
          [foralli(l2:<list A>).
             induction(l1:<list <list A>>) return { (foldr1 append l2 l1) = (append (concat l1) l2) }
             with
               nil _ => hypjoin (foldr1 append l2 l1) (append (concat l1) l2)
                        by l1_eq end
             | cons _ x l1' => 
               transs 
                 hypjoin (foldr1 append l2 l1) (append x (foldr1 append l2 l1'))
                   by l1_eq end
                 cong (append x *) [l1_IH l1']
                 symm [append_assoc A x (concat A l1') l2]
                 hypjoin (append (append x (concat l1')) l2) (append (concat l1) l2)
                 by l1_eq end
               end
             end
           (concat A l2) l1]
   end.

Define concat_concat_map1 
  : Forall(A B:type)(f:Fun(x:A).<list <list B>>)
          (fTot:Forall(x:A).Exists(y:<list <list B>>). { (f x) = y})
          (l:<list A>).
     { (concat (concat (map1 f l))) = (concat (map1 fun(x).(concat (f x)) l)) } :=
  foralli(A B:type)(f:Fun(x:A).<list <list B>>)
         (fTot:Forall(x:A).Exists(y:<list <list B>>). { (f x) = y}).
  induction(l:<list A>) return { (concat (concat (map1 f l))) = (concat (map1 fun(x).(concat (f x)) l)) }
  with
    nil _ => hypjoin (concat (concat (map1 f l))) (concat (map1 fun(x).(concat (f x)) l))
             by l_eq end
  | cons _ x l' => 
    transs hypjoin (concat (concat (map1 f l))) (concat (append (f x) (concat (map1 f l'))))
             by l_eq end
           [concat_append B terminates (f x) by fTot
              (concat <list B> (map1 A <list <list B>> f l'))]
           cong (append (concat (f x)) *) [l_IH l']
           hypjoin (append (concat (f x)) (concat (map1 fun(x). (concat (f x)) l')))
                   (concat (map1 fun(x).(concat (f x)) l))
           by l_eq end
    end
  end.

Define nth_append : Forall(A:type)(n:nat)(l:<list A>)(a:A)
                          (u:{(nth n l) = a}).
                       Exists(l1 l2:<list A>).
                         { l = (append l1 (cons a l2)) } :=
  foralli(A:type).
  induction(n:nat)(l:<list A>) 
    return Forall(a:A)
                 (u:{(nth n l) = a}).
           Exists(l1 l2:<list A>).
             { l = (append l1 (cons a l2)) } with
    nil _ => 
      foralli(a:A)
             (u:{(nth n l) = a}).
        contra
          transs symm u
                 hypjoin (nth n l) abort ! by l_eq end
                 aclash a
          end
        Exists(l1 l2:<list A>).
             { l = (append l1 (cons a l2)) } 
  | cons _ b l' => 
    foralli(a:A)
           (u:{(nth n l) = a}).
    case n with
      Z => 
      existsi (nil A) 
      Exists(l2:<list A>).
              { l = (append * (cons a l2)) } 
      existsi l'
         { l = (append nil (cons a *)) } 
         hypjoin l (append nil (cons a l'))
         by u l_eq n_eq end
    | S n' => 
      existse [l_IH n' l' a hypjoin (nth n' l') a by u n_eq l_eq end]
      foralli(l1 l2:<list A>)(u2:{ l' = (append l1 (cons a l2)) }).
        existsi (cons A b l1)
        Exists(l2:<list A>).
                { l = (append * (cons a l2)) } 
        existsi l2
          { l = (append (cons b l1) (cons a *)) } 
          hypjoin l (append (cons b l1) (cons a l2))
          by u2 l_eq end
    end
  end.
             

Define length : Fun(A: type)(^#owned l : <list A>).nat :=
	fun length (A: type)(^#owned l : <list A>) : nat.
	let c = Z in
	let ret =	
	    (foldr A nat nat c fun(^#owned cookie:nat)(^#owned a:A)(b:nat).(S b) Z l) in
	    do (dec nat c)
               ret
            end. 

Define length_tot 
  : Forall(A: type)(l : <list A>).Exists(n:nat). {(length A l) = n} :=
  foralli(A: type)(l : <list A>).
    existse 
      [foldrTot A nat nat Z fun(cookie:nat)(a:A)(b:nat).(S b) 
       foralli(a:A)(b:nat).
         existsi (S b) 
           { (fun(cookie)(a)(b).(S b) Z a b) = *}
           join (fun(cookie)(a)(b).(S b) Z a b) (S b)
       Z l]
    foralli(n:nat)(u:{(foldr Z fun(cookie)(a)(b).(S b) Z l) = n}).
    existsi n {(length A l) = *}
      trans join (length l)
                 (foldr Z fun(cookie)(a)(b).(S b) Z l)
            u.

Total length length_tot.

Define length_append
  : Forall(A:type)(l1 l2:<list A>).
     { (length (append l1 l2)) = (plus (length l1) (length l2)) } :=
  foralli(A:type)(l1 l2:<list A>).
    [induction(l1:<list A>) 
     return { (length (append l1 l2)) = (plus (length l1) (length l2)) }
     with
       nil ign => hypjoin (length (append l1 l2)) 
                          (plus (length l1) (length l2))
                  by l1_eq end
     | cons ign a l1' => 
       hypjoin (length (append l1 l2)) 
               (plus (length l1) (length l2))
       by l1_eq [l1_IH l1'] end
     end l1].

Define length_eq_Z 
  : Forall(A:type)(l:<list A>)
          (u:{ (length l) = Z}).
     { l = nil } :=
  foralli(A:type)(l:<list A>)
         (u:{ (length l) = Z}).
  case l with
    nil ign => l_eq
  | cons ign a l' => 
    contra
      trans
        hypjoin (S (length l')) (length l) 
        by l_eq end
      trans u
      clash Z (S terminates (length l') by length_tot)
    { l = nil }
  end.

Define length_eq_S 
  : Forall(A:type)(l:<list A>)(n:nat)
          (u:{ (length l) = (S n)}).
    Exists(a:A)(l':<list A>).
     { l = (cons a l') } :=
  foralli(A:type)(l:<list A>)(n:nat)
         (u:{ (length l) = (S n)}).
    case l with
      nil _ => 
      contra
        trans 
          trans join Z (length nil)
          trans cong (length *) symm l_eq
                u
          clash (S n) Z
      Exists(a:A)(l':<list A>).
         { l = (cons a l') } 
    | cons _ a l' => 
      existsi a Exists(l':<list A>).
                   { l = (cons * l') } 
      existsi l' {l = (cons a *) } 
        l_eq
    end.

Define singleton_eq_append 
 : Forall(A:type)(a1 a2:A)(l1 l2:<list A>)
         (u:{(cons a1 nil) = (append l1 (cons a2 l2)) }).
    Exists(u1:{ l1 = nil })
          (u2:{ a1 = a2 }).
      { l2 = nil } :=
 foralli(A:type)(a1 a2:A)(l1 l2:<list A>)
        (u:{(cons a1 nil) = (append l1 (cons a2 l2)) }).
 abbrev tl1 = terminates (length A l1) by length_tot in
 abbrev tl2 = terminates (length A l2) by length_tot in

 %- Z = sum of lengths l1, l2 -%
 abbrev P = 
     symm
     inj (S *)
       trans join (S Z) (length (cons a1 nil))
       trans cong (length *) u
       trans [length_append A l1 (cons A a2 l2)]
       trans cong (plus (length l1) *)
               join (length (cons a2 l2)) (S (length l2))
             [plusS tl1 tl2] in
 abbrev l1nil = 
   [length_eq_Z A l1
   [plus_eq_Z1 tl1 tl2 P]] in
 abbrev l2nil =
   [length_eq_Z A l2
   [plus_eq_Z2 tl1 tl2 P]] in

  andi l1nil 
  andi inj (cons * **)
       trans u
       trans cong (append * (cons a2 l2)) l1nil
         join (append nil (cons a2 l2)) (cons a2 l2)
  l2nil.
          
Define eq_append_split 
 : Forall(A:type)(l1 l2 l1' l2' : <list A>)
         (u1:{ (le (length l1) (length l1')) = tt })
         (u2:{ (append l1 l2) = (append l1' l2')}).
    Exists(lh : <list A>)
          (u3 : { l1' = (append l1 lh) }).
      { l2 = (append lh l2') } :=
 foralli(A:type).
 induction(l1:<list A>) 
 return Forall(l2 l1' l2' : <list A>)
              (u1:{ (le (length l1) (length l1')) = tt })
              (u2:{ (append l1 l2) = (append l1' l2')}).
        Exists(lh : <list A>)
              (u3 : { l1' = (append l1 lh) }).
          { l2 = (append lh l2') } 
 with
   nil _ => 
   foralli(l2 l1' l2' : <list A>)
          (u1:{ (le (length l1) (length l1')) = tt })
          (u2:{ (append l1 l2) = (append l1' l2')}).
     existsi l1'
         Exists(u3 : { l1' = (append l1 *) }).
           { l2 = (append * l2') } 
         andi hypjoin l1' (append l1 l1') by l1_eq end
              hypjoin l2 (append l1' l2') by l1_eq u2 end
 | cons _ a l1a => 
   foralli(l2 l1' l2' : <list A>)
          (u1:{ (le (length l1) (length l1')) = tt })
          (u2:{ (append l1 l2) = (append l1' l2')}).
   existse [le_S4 (length A l1a) (length A l1')
             symm
             trans symm u1
             trans cong (le (length *) (length l1')) l1_eq
                   join (le (length (cons a l1a)) (length l1')) (le (S (length l1a)) (length l1'))]
   foralli(c:nat)(u3:{ (length l1') = (S c) }).
   existse [length_eq_S A l1' c u3]
   foralli(a':A)(l1'a:<list A>)(l1'_eq:{ l1' = (cons a' l1'a) }).
     abbrev P = hypjoin (cons a (append l1a l2)) (cons a' (append l1'a l2'))
                by l1'_eq l1_eq u2 end in
     existse [l1_IH l1a l2 l1'a l2' 
                 symm
                 trans symm u1
                 trans cong (le (length *) (length l1')) l1_eq
                 trans cong (le (length (cons a l1a)) (length *)) l1'_eq
                 trans join (le (length (cons a l1a)) (length (cons a' l1'a))) (le (S (length l1a)) (S (length l1'a)))
                       [S_le_S (length A l1a) (length A l1'a)]
               inj (cons ** *) P]  
     foralli(lh:<list A>)(u4:{l1'a = (append l1a lh) })(u5:{l2 = (append lh l2')}).
       existsi lh
         Exists(u6 : { l1' = (append l1 *)}). { l2 = (append * l2') }
       andi trans l1'_eq
            trans cong (cons * l1'a) inj (cons * **) symm P
            trans cong (cons a *) u4
            trans join (cons a (append l1a lh)) (append (cons a l1a) lh)
                  cong (append * lh) symm l1_eq
       u5
 end.

Define eq_length_append 
 : Forall(A:type)(l1 l2 l1' l2':<list A>)
         (u1:{ (length l1) = (length l1') })
         (u2:{ (append l1 l2) = (append l1' l2') }).
    Exists(u3 : { l1 = l1' }). { l2 = l2' } :=
  foralli(A:type).
  induction(l1:<list A>) 
  return Forall(l2 l1' l2':<list A>)
               (u1:{ (length l1) = (length l1') })
               (u2:{ (append l1 l2) = (append l1' l2') }).
          Exists(u3 : { l1 = l1' }). { l2 = l2' } 
  with
    nil _ => 
    foralli(l2 l1' l2':<list A>)
           (u1:{ (length l1) = (length l1') })
           (u2:{ (append l1 l2) = (append l1' l2') }).
     abbrev l1'_eq = [length_eq_Z A l1' trans symm u1 
                                        trans cong (length *) l1_eq
                                              join (length nil) Z] in
     andi symm trans l1'_eq symm l1_eq
       trans join l2 (append nil l2)
       trans cong (append * l2) symm l1_eq
       trans u2
       trans cong (append * l2') l1'_eq
             join (append nil l2') l2'
  | cons _ a l1a => 
    foralli(l2 l1' l2':<list A>)
           (u1:{ (length l1) = (length l1') })
           (u2:{ (append l1 l2) = (append l1' l2') }).
    existse [length_eq_S A l1' (length A l1a)
               trans symm u1
               trans cong (length *) l1_eq
                     join (length (cons a l1a)) (S (length l1a))]
    foralli(a':A)(l1a':<list A>)(l1'_eq:{l1' = (cons a' l1a')}).
    abbrev P = hypjoin (cons a (append l1a l2)) (cons a' (append l1a' l2'))
               by u2 l1_eq l1'_eq end in
    existse
      [l1_IH l1a l2 l1a' l2' inj (S *) hypjoin (S (length l1a)) (S (length l1a')) by u1 l1_eq l1'_eq end
         inj (cons ** *) P]
      foralli(u3a: { l1a = l1a' })(u4: { l2 = l2' }).
         andi trans l1_eq
              trans cong (cons * l1a) inj (cons * **) P
              trans cong (cons a' *) u3a
                    symm l1'_eq
          u4
  end.

Define nth_length : Forall(A:type)(l1 l2:<list A>)(a:A).
                      { (nth (length l1) (append l1 (cons a l2))) = a } :=
  foralli(A:type)(l1 l2:<list A>)(a:A).
    [induction(l1:<list A>) return { (nth (length l1) (append l1 (cons a l2))) = a }
       with
       nil _ => hypjoin (nth (length l1) (append l1 (cons a l2))) a by l1_eq end
     | cons _ b l1' => hypjoin (nth (length l1) (append l1 (cons a l2))) a by l1_eq [l1_IH l1'] end
     end l1].

Define set_nth_length : Forall(A:type)(n:nat)(l:<list A>)(a:A)
                              (u:{(lt n (length l)) = tt }).
                         { (length (set_nth n l a)) = (length l) } :=
  foralli(A:type)(n:nat)(l:<list A>)(a:A)
         (u:{(lt n (length l)) = tt }).
   [induction(l:<list A>) return Forall(n:nat)(u:{(lt n (length l)) = tt }).
                                   { (length (set_nth n l a)) = (length l) } with
      nil _ =>
      foralli(n:nat)(u:{(lt n (length l)) = tt }). 
        contra
          transs symm [lt_Z n]
                 cong (lt n *) hypjoin Z (length l) by l_eq end
                 u
                 clash tt ff
           end
        { (length (set_nth n l a)) = (length l) } 
    | cons _ b l' => 
      foralli(n:nat)(u:{(lt n (length l)) = tt }). 
        case n with
          Z => 
          hypjoin (length (set_nth n l a)) (length l) 
          by l_eq n_eq end
        | S n' => 
          hypjoin (length (set_nth n l a)) (length l) 
            by l_eq n_eq [l_IH l' n' hypjoin (lt n' (length l')) tt 
                                       by u n_eq l_eq end] 
            end
        end
    end l n u].


Define eqlist : Fun(A:type)(eqA:Fun(^#owned x1 x2:A).bool)
                   (^#owned l1 l2:<list A>)
                   .bool :=
  fun eqlist(A:type)(eqA:Fun(^#owned x1 x2:A).bool)(^#owned l1 l2:<list A>):bool.
  match l1 by l1p l1t with
    nil A1 =>
      match l2 by l2p l2t with
        nil A2 => tt
      | cons A2 h2 t2 => ff
      end
  | cons A1 h1 t1 =>
      match l2 by l2p l2t with
        nil A2 => ff
      | cons A2 h2 t2 => (and (eqA h1 h2) (eqlist A eqA t1 t2))
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
                  existse [and_tot terminates (eqA h1cast h2cast) by eqA_total o2]
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

Define eqlist_refl :=
	foralli(A:type)(eqA:Fun(x1 x2:A).bool)
				 (eqA_refl:Forall(x:A).{ (eqA x x) = tt }).
  induction(c:<list A>) return { (eqlist eqA c c) = tt } with
    nil _ => hypjoin (eqlist eqA c c) tt by c_eq end
  | cons _ l c' =>
  		hypjoin (eqlist eqA c c) tt by c_eq [eqA_refl l] [c_IH c'] end
  end.
  

Define member : Fun(A:type)
                   (^#owned x:A)
                   (^#owned l:<list A>)
                   (eqA:Fun(^#owned x1 x2:A).bool).bool :=
  fun member(A:type)
            (^#owned x:A)
            (^#owned l:<list A>)
            (eqA:Fun(^#owned x1 x2:A).bool):bool.
  match l with
    nil A' => ff
  | cons A' h t => (or (eqA (clone_owned A x) h) (member A x t eqA))
  end.

Define member_total : Forall(A:type)
                            (x:A)
                            (l:<list A>)
                            (eqA:Fun(x1 x2:A).bool)
                            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
                      Exists(z:bool).
                        { (member x l eqA) = z } :=
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

Total member member_total.

Define member_or_append :
  Forall(A:type)
        (eq:Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (x:A)
        (l1:<list A>)(l2:<list A>).
    { (or (member x l1 eq) (member x l2 eq))
      = (member x (append l1 l2) eq) }
  :=
  foralli(A:type)
         (eq:Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (x:A).
  induction(l1:<list A>)
    return Forall(l2:<list A>).
             { (or (member x l1 eq) (member x l2 eq))
               = (member x (append l1 l2) eq) }
  with
    nil _ =>
      foralli(l2:<list A>).
      existse [member_total A x l2 eq eq_tot]
        foralli(z2:bool)(z2_pf:{(member x l2 eq) = z2}).
      hypjoin (or (member x l1 eq) (member x l2 eq))
              (member x (append l1 l2) eq)
        by l1_eq z2_pf [append_nil A l1] [or_comm ff z2] [or_def2ff z2] end
  | cons _ a l1' =>
      foralli(l2:<list A>).
      existse [eq_tot x a]
        foralli(za:bool)(za_pf:{(eq x a) = za}).
      existse [member_total A x l1' eq eq_tot]
        foralli(z1':bool)(z1'_pf:{(member x l1' eq) = z1'}).
      existse [member_total A x l2 eq eq_tot]
        foralli(z2:bool)(z2_pf:{(member x l2 eq) = z2}).
      trans hypjoin (or (member x l1 eq) (member x l2 eq))
                    (or (or za z1') z2) by l1_eq za_pf z1'_pf z2_pf end
      trans [or_assoc za z1' z2]
      trans hypjoin (or za (or z1' z2))
                    (or (eq x a) (or (member x l1' eq) (member x l2 eq)))
              by l1_eq za_pf z1'_pf z2_pf end
      trans cong (or (eq x a) *) [l1_IH l1' l2]
            hypjoin (or (eq x a) (member x (append l1' l2) eq))
                    (member x (append l1 l2) eq)
              by l1_eq end
            
  end.

Define member_tt_append :
  Forall(A:type)
        (eq:Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (a:A)(l1:<list A>)(l2:<list A>)
        (u1: {(member a l1 eq) = tt}).
        { (member a (append l1 l2) eq) = tt }
  :=
  foralli(A:type)
         (eq:Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (a:A)(l1:<list A>)(l2:<list A>)
         (u1: {(member a l1 eq) = tt}).
  trans symm [member_or_append A eq eq_tot a l1 l2]
  trans cong (or * (member a l2 eq)) u1
  trans [or_comm tt (member A a l2 eq)]
        [or_tt (member A a l2 eq)]
	.

Define member_tt_cons :
  Forall(A:type)
        (eq:Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (a:A)(l:<list A>)(b:A)
        (u: {(member a l eq) = tt}).
        { (member a (cons b l) eq) = tt }
  :=
  foralli(A:type)
         (eq:Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (a:A)(l:<list A>)(b:A)
         (u: {(member a l eq) = tt}).
  existse [eq_tot a b]
    foralli(z:bool)(z_eq:{ (eq a b) = z }).
  trans hypjoin (member a (cons b l) eq)
                (or z tt)
          by u z_eq end
        [or_tt z]
	.

Define member_tt_append_front :
  Forall(A:type)
        (eq:Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (a:A)(l1:<list A>)(l2:<list A>)
        (u1: {(member a l1 eq) = tt}).
        { (member a (append l2 l1) eq) = tt }
  :=
  foralli(A:type)
         (eq:Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (a:A)(l1:<list A>)(l2:<list A>)
         (u1: {(member a l1 eq) = tt}).
  trans symm [member_or_append A eq eq_tot a l2 l1]
        % (member a l2++l1) = (or (member a l2) (member a l1))
  trans cong (or (member a l2 eq) *) u1
        % = (or (member a l2) tt)
        [or_tt (member A a l2 eq)]
	.

Define member_cons_ff_member :
  Forall(A:type)
        (eq:Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (a b:A)(l:<list A>)
        (u: {(member a (cons b l) eq) = ff}).
    { (member a l eq) = ff }
  :=
  foralli(A:type)
         (eq:Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (a b:A)(l:<list A>)
         (u: {(member a (cons b l) eq) = ff}).
  existse [eq_tot a b]
    foralli(z1:bool)(z1_pf:{ (eq a b) = z1 }).
  existse [member_total A a l eq eq_tot]
    foralli(z2:bool)(z2_pf:{ (member a l eq) = z2 }).
  abbrev p1 = 
    hypjoin (or z1 z2) ff
      by u z1_pf z2_pf end
  in
  trans z2_pf
        [or_ffr z1 z2 p1]
  .

Define member_append_cons : 
  Forall(A:type)(a:A)(l1 l2:<list A>)
        (eq : Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (eq_refl : Forall(a:A). { (eq a a) = tt}).
    { (member a (append l1 (cons a l2)) eq) = tt } :=
  foralli(A:type)(a:A)(l1 l2:<list A>)
         (eq : Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (eq_refl : Forall(a:A). { (eq a a) = tt}).
    [member_tt_append_front A eq eq_tot a (cons A a l2) l1
      hypjoin (member a (cons a l2) eq) tt by [eq_refl a] end].

Define member_append_cons2 : 
  Forall(A:type)(a:A)(l1 l2:<list A>)
        (eq : Fun(a b:A).bool)
        (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
        (eq_refl : Forall(a:A). { (eq a a) = tt}).
    { (member a (append (cons a l1) l2) eq) = tt } :=
  foralli(A:type)(a:A)(l1 l2:<list A>)
         (eq : Fun(a b:A).bool)
         (eq_tot:Forall(a b:A).Exists(z:bool).{ (eq a b) = z })
         (eq_refl : Forall(a:A). { (eq a a) = tt}).
    [member_tt_append A eq eq_tot a (cons A a l1) l2
      hypjoin (member a (cons a l1) eq) tt by [eq_refl a] end].

Define list_exists : Fun(A C:type)(^#owned c:C)

                      (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<list A>).bool :=

fun(A C:type)(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).

  (foldr A bool C c fun(^#owned c:C)(^#owned a:A)(b:bool).(or (f c a) b) ff).

Define list_forall : Fun(A C:type)(^#owned c:C)
                (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<list A>).bool :=
  fun(A C:type)(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).
    (foldr A bool C c fun(^#owned c:C)(^#owned a:A)(b:bool).(and (f c a) b) tt).


Define fill : Fun(A:type)(^#owned a:A)(^#owned n:nat).<list A> :=
  fun fill(A:type)(^#owned a:A)(^#owned n:nat):<list A>.
    match n with
      Z => (nil A)
    | S n' => (cons A (inc_owned A a) (fill A a n'))
    end.


Define length_fill : Forall (A : type) (a : A) (n : nat) .
  { (length (fill a n)) = n } :=
  foralli (A : type) (a : A) .
  induction (n : nat) return { (length (fill a n)) = n }
  with
      Z    =>
        trans cong (length (fill a *)) n_eq
        trans join (length (fill a Z)) Z
              symm n_eq
    | S x' =>
        trans cong (length (fill a *)) n_eq
        trans join (length (fill a (S x'))) (S (length (fill a x')))
        trans cong (S *) [n_IH x']
              symm n_eq
  end.

% early terminating version of list_forall/_exists (not using foldl)
Define list_all : Fun(A:type)(f:Fun(a:A).bool)(l:<list A>) . bool :=
  fun list_all (A:type)(f:Fun(a:A).bool)(l:<list A>) : bool .
    match l with
      nil _ => tt
    | cons _ a l' => match (f a) with
                       ff =>  ff
                     | tt =>  (list_all A f l')
                     end
    end.

Define list_all_append :
  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (l1 l2:<list A>)(u:{(list_all f l1) = tt}).
   {(list_all f (append l1 l2)) = (list_all f l2)} :=
foralli(A:type)(f:Fun(a:A).bool)(ftot: Forall(a:A).Exists(b:bool).{(f a) = b})(l1 l2:<list A>)(u:{(list_all f l1) = tt}).
[
induction (l1:<list A>) return 
Forall(u:{(list_all f l1) = tt}).{(list_all f (append l1 l2)) = (list_all f l2)} 
with

         nil _ =>  foralli(u:{(list_all f l1) = tt}).
		   trans cong (list_all f (append * l2))l1_eq
                         join (list_all f (append nil l2))(list_all f l2)
   
| cons _ a l1' => foralli(u:{(list_all f l1) = tt}).
		  case terminates (f a) by ftot by v ign with
                     ff => contra
                           trans symm u
			   trans hypjoin (list_all f l1) ff by l1_eq v end
                                 clash ff tt
                           {(list_all f (append l1 l2)) = (list_all f l2)}

                                                      
                   | tt => trans hypjoin (list_all f (append l1 l2)) (list_all f (append l1' l2)) by l1_eq v end
			   abbrev l1'_tt = symm trans symm u
                                           hypjoin (list_all f l1) (list_all f l1') by l1_eq v end in
                           [l1_IH l1' l1'_tt]
                           
                           end
                                    
end
l1 u].

Define list_all_append2 :
  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (l1 l2:<list A>)
        (u: {(list_all f (append l1 l2)) = tt}).
    {(list_all f l1) = tt} :=
  foralli(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b}).
  induction(l1:<list A>) 
  return Forall(l2:<list A>)
               (u: {(list_all f (append l1 l2)) = tt}).
            {(list_all f l1) = tt} with
    nil _ => 
      foralli(l2:<list A>)
             (u: {(list_all f (append l1 l2)) = tt}).
        hypjoin (list_all f l1) tt by l1_eq end
  | cons _ a l1' =>
      foralli(l2:<list A>)
             (u: {(list_all f (append l1 l2)) = tt}).
      case terminates (f a) by ftot by fa _ with
        ff => contra
                transs symm u 
                       hypjoin (list_all f (append l1 l2)) ff by fa l1_eq end
                       clash ff tt
                end
              {(list_all f l1) = tt}
      | tt => hypjoin (list_all f l1) tt
              by l1_eq fa
                 [l1_IH l1' l2
                   hypjoin (list_all f (append l1' l2)) tt 
                   by fa l1_eq u end]
              end 
      end
  end.

Define list_all_append3 :
  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (l1 l2:<list A>)
        (u: {(list_all f (append l1 l2)) = tt}).
    {(list_all f l2) = tt} :=
  foralli(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
         (l1 l2:<list A>)
         (u: {(list_all f (append l1 l2)) = tt}).
    symm 
    trans symm u
      [list_all_append A f ftot l1 l2 
         [list_all_append2 A f ftot l1 l2 u]].

Define list_all_total :
  Forall(A:type)
        (f:Fun(a:A).bool)
        (f_tot:Forall(x:A).Exists(y:bool).{ (f x) = y })
        (l:<list A>).
  Exists(z:bool). { (list_all A f l) = z }
  :=
  foralli(A:type)
         (f:Fun(a:A).bool)
         (f_tot:Forall(x:A).Exists(y:bool).{ (f x) = y }).
  induction(l:<list A>) return Exists(z:bool). { (list_all A f l) = z }
  with
    nil _ =>
      existsi tt { (list_all A f l) = * }
        hypjoin (list_all A f l) tt by l_eq end
  | cons _ a l' =>
      existse [f_tot a]
      foralli(y:bool)(y_pf:{ (f a) = y }).
      case y with
        ff =>
          existsi ff { (list_all A f l) = * }
            hypjoin (list_all A f l) ff by l_eq y_pf y_eq end
      | tt =>
          existse [l_IH l']
          foralli(z:bool)(z_pf:{ (list_all A f l') = z }).
          existsi z { (list_all A f l) = * }
            hypjoin (list_all A f l) z by l_eq y_pf y_eq z_pf end
      end
  end
  .

Define list_all_cons_tt_head :
  Forall(A:type)
        (f:Fun(a:A).bool)
        (a:A)(l:<list A>)
        (u:{ (list_all f (cons a l)) = tt }).
    { (f a) = tt }
  :=
  foralli(A:type)
         (f:Fun(a:A).bool)
         (a:A)(l:<list A>)
         (u:{ (list_all f (cons a l)) = tt }).
  abbrev p1 = eval (list_all f (cons a l)) in
  abbrev p2 = cinv (f a) trans symm p1 u in
  existse p2
  foralli(z1:bool)(z1_pf:{ (f a) = z1 }).
  case z1 with
    ff => contra
            trans symm u
            trans hypjoin (list_all f (cons a l)) ff by z1_pf z1_eq end
                  clash ff tt
            { (f a) = tt }
  | tt => hypjoin (f a) tt by z1_pf z1_eq end
  end
  .

Define  list_all_cons_tt_tail :
  Forall(A:type)
        (f:Fun(a:A).bool)
        (a:A)(l:<list A>)
        (u:{ (list_all f (cons a l)) = tt }).
    { (list_all f l) = tt }
  :=
  foralli(A:type)
         (f:Fun(a:A).bool)
         (a:A)(l:<list A>)
         (u:{ (list_all f (cons a l)) = tt }).
  abbrev p1 = eval (list_all f (cons a l)) in
  abbrev p2 = cinv (f a) trans symm p1 u in
  existse p2
  foralli(z1:bool)(z1_pf:{ (f a) = z1 }).
  case z1 with
    ff => contra
            trans symm u
            trans hypjoin (list_all f (cons a l)) ff by z1_pf z1_eq end
                  clash ff tt
            { (list_all f l) = tt }
  | tt => hypjoin (list_all f l) tt by z1_pf z1_eq u end
  end
  .

Define list_all_set_nth :
  Forall(A:type)(n:nat)(l:<list A>)(a:A)
        (f:Fun(a:A).bool)
        (u1 : { (lt n (length l)) = tt })
        (u2 : { (list_all f l) = tt })
        (u3 : { (f a) = tt }).
   { (list_all f (set_nth n l a)) = tt } :=
  foralli(A:type)(n:nat)(l:<list A>)(a:A)
         (f:Fun(a:A).bool)
         (u1 : { (lt n (length l)) = tt })
         (u2 : { (list_all f l) = tt })
         (u3 : { (f a) = tt }).
  [induction(l:<list A>) return Forall(n:nat)(u1 : { (lt n (length l)) = tt })
                                      (u2 : { (list_all f l) = tt }).
                                  { (list_all f (set_nth n l a)) = tt } with
     nil _ => foralli(n:nat)(u1 : { (lt n (length l)) = tt })
                     (u2 : { (list_all f l) = tt }).
              contra
                transs symm [lt_Z n]
                       cong (lt n *) hypjoin Z (length l) by l_eq end
                       u1
                       clash tt ff
                end
              { (list_all f (set_nth n l a)) = tt } 
   | cons _ b l' => 
     foralli(n:nat)(u1 : { (lt n (length l)) = tt })
            (u2 : { (list_all f l) = tt }).
       abbrev P = trans symm cong (list_all f *) l_eq u2 in
       case n with
         Z =>
           hypjoin (list_all f (set_nth n l a)) tt 
           by n_eq l_eq u3 
              [list_all_cons_tt_tail A f b l' P]
           end
      | S n' => 
           hypjoin (list_all f (set_nth n l a)) tt 
           by n_eq l_eq u3 
              [list_all_cons_tt_head A f b l' P]
              [l_IH l' n' hypjoin (lt n' (length l')) tt 
                            by u1 n_eq l_eq end
                [list_all_cons_tt_tail A f b l' P]]
           end
      end
   end l n u1 u2].

Define list_all_nth : Forall(A:type)(n:nat)(l:<list A>)(a:A)
                            (f:Fun(a:A).bool)
                            (ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
                            (u1:{(nth n l) = a})
                            (u2:{(list_all f l) = tt}).
                       { (f a) = tt } :=
 foralli(A:type)(n:nat)(l:<list A>)(a:A)
        (f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
        (u1:{(nth n l) = a})
        (u2:{(list_all f l) = tt}).
  existse [nth_append A n l a u1]
  foralli(l1 l2:<list A>)(u3:{l = (append l1 (cons a l2))}).
    [list_all_cons_tt_head A f a l2
      [list_all_append3 A f ftot l1 (cons A a l2)
         hypjoin (list_all f (append l1 (cons a l2))) tt
         by u3 u2 end]].    

Define list_all_implies :
  Forall(A:type)
        (f1 f2:Fun(a:A).bool)
        (fimp : Forall(a:A)(u:{(f1 a) = tt}). { (f2 a) = tt })
        (l:<list A>)
        (u : {(list_all f1 l) = tt }).
  {(list_all f2 l) = tt } :=
  foralli(A:type)
         (f1 f2:Fun(a:A).bool)
         (fimp : Forall(a:A)(u:{(f1 a) = tt}). { (f2 a) = tt }).
    induction(l:<list A>) 
      return Forall(u : {(list_all f1 l) = tt }). {(list_all f2 l) = tt } with
      nil _ => foralli(u : {(list_all f1 l) = tt }).
                 hypjoin (list_all f2 l) tt by l_eq end
    | cons _ a l' =>
      foralli(u : {(list_all f1 l) = tt }).
        abbrev P = trans symm cong (list_all f1 *) l_eq u in
          hypjoin (list_all f2 l) tt
            by l_eq 
               [fimp a [list_all_cons_tt_head A f1 a l' P]]
               [l_IH l' [list_all_cons_tt_tail A f1 a l' P]]
            end
    end. 


Define list_any : Fun(A:type)(f:Fun(^#owned a:A).bool)(^#owned l:<list A>) . bool :=
  fun list_any (A:type)(f:Fun(^#owned a:A).bool)(^#owned l:<list A>) : bool .
    match l with
      nil _ => ff
    | cons _ a l' => match (f a) with
                       ff =>  (list_any A f l')
                     | tt =>  tt
                     end
    end.

