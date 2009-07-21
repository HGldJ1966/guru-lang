%Set "show_includes".

Include "plus.g".
Include "unit.g".
Include "pair.g". % for foldl'

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
      nil A' => do (consume_owned C cookie) b end
   | cons A' a' l' => (fcn cookie a' 
                         (foldr A B C (clone_owned C cookie) fcn b l'))
   end. 

Define foldl : Fun(A B : type) (fcn : Fun (x : A) (y : B) . B) (b : B)
  (l : <list A>) . B :=
  fun foldl (A B : type) (fcn : Fun (x : A) (y : B) . B) (b : B)
    (l : <list A>) : B .
    match l with
        nil _ => b
      | cons _ a' l' => (foldl A B fcn (fcn a' b) l')
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
  fun nth(A:type)(n:nat)(l:<list A>)(b:A):<list A>.
    match l with
      nil _ => abort <list A>
    | cons _ a l' =>
      match n with
        Z => (cons A b l')
      | S n' => (cons A a (nth A n' l' b))
      end
    end.

Define filter : Fun(A:type)(f:Fun(a:A).bool)(l1:<list A>) . <list A> :=
  fun filter (A:type)(f:Fun(a:A).bool)(l1:<list A>) : <list A> .
     match l1 with
        nil _ => (nil A)
     | cons _ a l' => match (f a) with 
                        ff => (filter A f l')
                      | tt => (cons A a (filter A f l'))
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
  | cons A' h t => (or (eqA x h) (member A x t eqA))
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

Define list_exists : Fun(A C:type)(^#owned c:C)
                      (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<list A>).bool :=
fun(A C:type)(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).
  (foldr A bool C c fun(^#owned c:C)(^#owned a:A)(b:bool).(or (f c a) b) ff).

Define list_forall : Fun(A C:type)(^#owned c:C)
                (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<list A>).bool :=
  fun(A C:type)(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).
    (foldr A bool C c fun(^#owned c:C)(^#owned a:A)(b:bool).(and (f c a) b) tt).


% foldl with early termination
%-
fcn should return a pair of bool and B types
  the first value of the pair decides whether to continue or not
    if it is ff, terminates; otherwise, continues.
  the second value is the return value of the function for (original) foldl.
-%
Define foldl2 :
  Fun(A B : type)
     (fcn : Fun(x:A)(y:B).<pair bool B>)
     (b : B)
     (l : <list A>). B
  :=
  fun foldl2(A B:type)(fcn:Fun(x:A)(y:B).<pair bool B>)
            (b:B)(l:<list A>) : B.
    match l with
      nil _ => b
    | cons _ a' l' =>
       match (fcn a' b) with
         mkpair _ _ cont b' =>
           match cont with
             ff => (foldl2 A B fcn b' (nil A))  % early termination with new value
           | tt => (foldl2 A B fcn b' l')
           end
       end
    end
  .

Define list_exists2 : Fun(A:type)
                         (f:Fun(a:A).bool)
                         (l:<list A>).bool
  :=
  fun(A:type)(f:Fun(a:A).bool).
    let f' =
      fun(a:A)(b:bool).
        let b' = (or (f a) b) in
        (mkpair bool bool (not b') b')
    in
    (foldl2 A bool f' ff).

Define list_forall2 : Fun(A:type)
                         (f:Fun(a:A).bool)
                         (l:<list A>).bool
  :=
  fun(A:type)(f:Fun(a:A).bool).
    let f' =
      fun(a:A)(b:bool).
        let b' = (and (f a) b) in
        (mkpair bool bool b' b')
    in
    (foldl2 A bool f' tt).


Define fill : Fun(A:type)(^#owned a:A)(^#owned n:nat).<list A> :=
  fun fill(A:type)(^#owned a:A)(^#owned n:nat):<list A>.
    match n with
      Z => (nil A)
    | S n' => (cons A (inc A a) (fill A a n'))
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

Define list_all_append:  Forall(A:type)(f:Fun(a:A).bool)(ftot : Forall(a:A).Exists(b:bool). {(f a) = b})
(l1 l2:<list A>)(u:{(list_all f l1) = tt}).{(list_all f (append l1 l2)) = (list_all f l2)} :=
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


Define list_any : Fun(A:type)(f:Fun(^#owned a:A).bool)(^#owned l:<list A>) . bool :=
  fun list_any (A:type)(f:Fun(^#owned a:A).bool)(^#owned l:<list A>) : bool .
    match l with
      nil _ => ff
    | cons _ a l' => match (f a) with
                       ff =>  (list_any A f l')
                     | tt =>  tt
                     end
    end.

% member (early terminating)
Define member2 : Fun(A:type)
                    (eqA:Fun(^#owned x1 x2:A).bool)
                    (^#owned x:A)
                    (^#owned l:<list A>).bool :=
  fun(A:type)
     (eqA:Fun(^#owned x1 x2:A).bool)
     (^#owned x:A)
     (^#owned l:<list A>).
  (list_any A (eqA x) l).

% l1 is a subset of l2
Define list_subset : Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) . bool :=
  fun list_subset (A:type)(eqA:Fun(^ #owned a b:A).bool)(l1 l2:<list A>) : bool .
                     (list_all A fun(a:A).(member A a l2 eqA) l1).


Define list_seteq: Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2 :<list A>). bool := 
   fun list_seteq (A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) : bool.
                   (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)).


Define list_intersect : Fun(A:type)(eqA : Fun(^ #owned a b: A).bool)(l1 l2:<list A>) . <list A> :=
  fun list_intersect (A:type)(eqA:Fun(^ #owned a b:A).bool)(l1 l2:<list A>) : <list A> .
                     (filter A fun(a:A).(member A a l2 eqA) l1).


Define append_helper : Forall(A:type)(a:A)(eqA : Fun(^ #owned a b: A).bool)(l'' l' : <list A>). {(append l' (cons a l'')) = (append (append l' (cons a nil)) l'')} :=
   foralli(A:type)(a:A)(eqA : Fun(^ #owned a b: A).bool)( l'' : <list A>).
     induction(l' : <list A>) return  {(append l' (cons a l'')) = (append (append l' (cons a nil)) l'')} with
         nil _ =>
                  trans cong (append * (cons a l'')) l'_eq
                  trans join (append nil (cons a l'')) (append (append nil (cons a nil)) l'')
                        cong (append (append * (cons a nil)) l'') symm l'_eq

       | cons _ b k =>
                       trans cong (append * (cons a l'')) l'_eq
                       trans join (append (cons b k) (cons a l'')) (append (cons b nil)(append k (cons a l'')))
                       trans cong (append (cons b nil) *) [l'_IH k]
                       trans join (append (cons b nil) (append (append k (cons a nil)) l''))
                                  (append (append (cons b k) (cons a nil)) l'')
                             cong (append (append * (cons a nil)) l'') symm l'_eq


       end.


Define list_setmember: Forall(A:type)(a:A)
                         (eqA:Fun(^ #owned x y: A).bool)
                         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
                         (u:{(eqA a a)= tt})(l'' l':<list A>).
                         { (member a (append l' (cons a l'')) eqA) = tt } :=
   foralli(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)
          (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
          (u: {(eqA a a) = tt})(l'':<list A>).
       induction(l':<list A>) return  { (member a (append l' (cons a l'')) eqA) = tt } with

        nil _ =>
               trans cong (member a (append * (cons a l'')) eqA) l'_eq
                     hypjoin (member a (append nil (cons a l'')) eqA) tt by u end

     | cons _ b k =>
                   trans cong (member a (append * (cons a l'')) eqA) l'_eq
                   trans join (member a (append (cons b k) (cons a l'')) eqA)
                        (member a (append (cons b nil) (append k (cons a l''))) eqA)
                   trans join (member a (append (cons b nil) (append k (cons a l''))) eqA)
                        (member a (append (cons b k) (cons a l'')) eqA)
                   trans join (member a (append (cons b k) (cons a l'')) eqA)
                        (member a (append (cons b nil) (append k (cons a l''))) eqA)
                   case terminates (eqA a b) by eqA_total by eqAp eqAt with
                         default bool => hypjoin (member a (append (cons b nil) (append k (cons a l''))) eqA)
                                         tt by eqAp [l'_IH k] end
                       end  
    end.


Define list_SubsetOfSelf : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
                            (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
                            (u: Forall(a:A).{(eqA a a ) = tt})
                            (l : <list A>).
                            Forall(l': <list A>).{(list_subset A eqA l (append l' l)) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
          (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
          (u: Forall(a:A). {(eqA a a ) = tt}).
        induction(l : <list A>) return Forall(l':<list A>).{(list_subset A eqA l (append l' l)) = tt} with
             nil _ => foralli(l': <list A>).
                        trans cong (list_subset eqA * (append l' *)) l_eq
                              join (list_subset eqA nil (append l' nil)) tt
           | cons _ a l'' =>  foralli(l': <list A>).
                                trans cong (list_subset eqA * (append l' *)) l_eq
                                trans hypjoin (list_subset eqA (cons a l'')(append l' (cons a l'')))
                                              (list_subset eqA l'' (append l' (cons a l'')))
                                              by [list_setmember A a eqA eqA_total [u a] l'' l' ] end
                                trans cong (list_subset eqA A l'' *) [append_helper A a eqA l'' l' ]
                                [l_IH l'' (append A l' (cons A a (nil A))) ]


           end.


Define member_trans_lemma: Forall(A:type)(a:A)(eqA :Fun(^ #owned a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2: <list A>) (u: {(member A a l1 eqA) = tt})(v:{(list_subset eqA l1 l2) = tt}) 
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
					{(member A a l2 eqA) = tt} :=
	foralli (A:type)(a:A)(eqA :Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	   induction(l1: <list A>) return Forall(l2:<list A>)(u: {(member A a l1 eqA) = tt})
		    (v:{(list_subset eqA l1 l2) = tt})(eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			{(member A a l2 eqA) = tt} with
	  	nil _ => foralli (l2:<list A>)(u: {(member A a l1 eqA) = tt})
				 (v:{(list_subset eqA l1 l2) = tt})
				 (eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			contra
			trans symm u
			trans cong (member A a * eqA) l1_eq
			trans join (member A a nil eqA) ff
			clash ff tt
			{(member A a l2 eqA) = tt}
				
	    | cons _ b l1' => foralli (l2:<list A>)(u: {(member A a l1 eqA) = tt})
				      (v:{(list_subset eqA l1 l2) = tt})
				      (eqA_to_equals:Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).			
				case terminates (eqA a b) by eqA_total by eqAp eqAt with
				   ff => 						
					case terminates (member A b l2 eqA) by member_total by memp memt with
					   ff => contra
						 trans symm v
						 trans hypjoin (list_subset eqA l1 l2) ff by memp l1_eq end
						 clash ff tt
						 {(member A a l2 eqA) = tt}
					| tt => 
					 abbrev H = symm hypjoin tt (list_subset eqA l1' l2) by memp l1_eq u v end in
					 abbrev H2 = hypjoin (member A a l1' eqA) tt by eqAp u l1_eq end in
					 [l1_IH l1' l2 H2 H eqA_to_equals]
					 end
				| tt => 			
				    case terminates (member A b l2 eqA) by member_total by memp memt with
					ff => contra
					      trans symm v
					      trans hypjoin (list_subset eqA l1 l2) ff by memp l1_eq end
					      clash ff tt
					      {(member A a l2 eqA) = tt}
				      | tt => hypjoin (member A a l2 eqA) tt by memp eqAp [eqA_to_equals a b eqAp] end
									
				      end
				end
				
	  end.


Define list_transitivity : Forall(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
				 (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
				 {(list_subset eqA l1 l3) = tt} :=
    foralli(A:type)(eqA: Fun(a b: A).bool)(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	induction(l1: <list A>) return Forall(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
					     (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
					     (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
					     {(list_subset eqA l1 l3) = tt} with
	     nil _ => foralli(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})(v:{(list_subset eqA l2 l3) = tt})
			(w:Forall(a:A).{(eqA a a) = tt})(eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			hypjoin (list_subset eqA l1 l3) tt by l1_eq end
	   | cons _ a l1' =>  foralli(l2 l3: <list A>)(u:{(list_subset eqA l1 l2) = tt})
		                     (v:{(list_subset eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
                                     (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
			
			abbrev l1'_subset_l3 =
			abbrev U1 =
			abbrev U1' =		
			symm trans symm hypjoin (list_subset eqA l1' (cons a l1')) tt by 
			                        [list_SubsetOfSelf A eqA eqA_total w l1' (cons A a (nil A)) ] end
			     symm cong (list_subset eqA l1' * ) l1_eq in
			[l1_IH l1' l1 l2 U1' u w eqA_to_equals] in
			[l1_IH l1' l2 l3 U1 v w eqA_to_equals] in

			abbrev a_in_l3 = 
			abbrev a_in_l2 = 
			abbrev a_in_l1 = hypjoin (member A a l1 eqA) tt by [w a] l1_eq end in
			hypjoin (member A a l2 eqA) tt by 
				[member_trans_lemma A a eqA eqA_total l1 l2 a_in_l1 u eqA_to_equals] end in

			hypjoin (member A a l3 eqA) tt by 
				[member_trans_lemma A a eqA eqA_total l2 l3 a_in_l2 v eqA_to_equals] end  in

			hypjoin (list_subset eqA l1 l3) tt by l1_eq l1'_subset_l3 a_in_l3 end
			


			
			
	   end.

Define list_subset_total :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>).
  Exists(x:bool).
    { (list_subset A eqA l1 l2) = x } :=
  foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
		   (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	induction(l1: <list A>) return Forall(l2:<list A>).Exists(z:bool).{(list_subset eqA l1 l2) = z} with
	   nil _ => foralli(l2:<list A>).
		      existsi tt {(list_subset eqA l1 l2) = * } 
			  hypjoin (list_subset eqA l1 l2) tt by l1_eq end
	 | cons _ a t => foralli(l2:<list A>).
			   case terminates (member A a l2 eqA) by member_total by memp memt with
				  ff => existsi ff {(list_subset eqA l1 l2) = * }
					   hypjoin (list_subset eqA l1 l2) ff by l1_eq  memp end
				| tt => existsi terminates (list_subset A eqA t l2) by [l1_IH t]
							 {(list_subset eqA l1 l2) = *}
					   hypjoin (list_subset eqA l1 l2) (list_subset eqA t l2) by memp l1_eq end
					
					
				end
				
	 end.
                                              

Define list_seteq_total :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2:<list A>).
  Exists(x:bool).
    { (list_seteq A eqA l1 l2) = x } :=
  foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
			         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z }).
	    induction(l1 : <list A>) return Forall(l2 :<list A>). Exists(z:bool).{(list_seteq eqA l1 l2) = z} with
		 nil _ => foralli(l2: <list A>).
		            case l2 with
			      nil _ => existsi tt {(list_seteq eqA l1 l2) = * }
					  hypjoin (list_seteq eqA l1 l2) tt by l1_eq l2_eq end
			    | cons _ b w => existsi ff {(list_seteq eqA l1 l2) = *}
					  hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq end
			    end
	      |  cons _ a t => foralli(l2: <list A>).
		                 case l2 with
				     nil _ => existsi ff {(list_seteq eqA l1 l2) = *}
						 hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq end
				   | cons _ b' w' => case terminates (list_subset A eqA l1 l2) by 
								list_subset_total by lsp lst with
						ff => existsi ff {(list_seteq eqA l1 l2) = *}
								hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq lsp end
					      | tt => case terminates (list_subset A eqA l2 l1) by
						  list_subset_total by lsp2 lst2 with
						     ff => existsi ff {(list_seteq eqA l1 l2) = *}
							  hypjoin (list_seteq eqA l1 l2) ff by l1_eq l2_eq lsp lsp2 end
						   | tt => existsi tt {(list_seteq eqA l1 l2) = *}
							  hypjoin (list_seteq eqA l1 l2) tt by l1_eq l2_eq lsp lsp2 end
						   end
					     end
				   end
	      end.



Define equal_to_subset : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
		(u:{ (list_seteq eqA l1 l2) = tt}).
		{(list_subset eqA l1 l2) = tt} :=
	foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2: <list A>) 
		(u:{ (list_seteq eqA l1 l2) = tt}).
		abbrev u' = hypjoin  (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	  [andtt_e1 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2]
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1] u']
	.

Define list_seteq_reflx : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
	(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(u:Forall(a:A).{(eqA a a) = tt})(l: <list A>).
		{(list_seteq eqA l l) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
	(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(u:Forall(a:A).{(eqA a a) = tt})(l: <list A>).
	
	
	abbrev u' = hypjoin (list_subset eqA l l) tt by [list_SubsetOfSelf A eqA eqA_total u l (nil A)] end in
	symm trans symm u'
	hypjoin (list_subset eqA l l) (list_seteq eqA l l ) by u' end
	
.

Define list_seteq_symm : Forall(A:type)(eqA : Fun(^ #owned a b: A).bool)
		(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
		(u:{ (list_seteq eqA l1 l2) = tt}).
		{(list_seteq eqA l2 l1) = tt} :=
   foralli(A:type)(eqA : Fun(^ #owned a b: A).bool)
	  (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })(l1 l2 :<list A>)
	  (u:{ (list_seteq eqA l1 l2) = tt}).
	
	abbrev A1 =	
	abbrev u' = hypjoin  (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	   [andtt_e1 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2]
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1 ] u'] in
	
	abbrev A2 = 
	abbrev v' = hypjoin (and (list_subset A eqA l1 l2)(list_subset A eqA l2 l1)) tt by u end in
	   [andtt_e2 terminates (list_subset A eqA l1 l2) by [list_subset_total A eqA eqA_total l1 l2] 
		    terminates (list_subset A eqA l2 l1) by [list_subset_total A eqA eqA_total l2 l1 ] v'] in
	
	symm trans symm u
	     trans hypjoin (list_seteq A eqA l1 l2) (list_subset A eqA l1 l2) by 
			   u [equal_to_subset A eqA eqA_total l1 l2 u] end
	     hypjoin (list_subset A eqA l1 l2)(list_seteq A eqA l2 l1) by A1 A2 end
	
.

Define list_seteq_trans: Forall(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_seteq eqA l1 l2) = tt})
				 (v:{(list_seteq eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
				 { (list_seteq eqA l1 l3) = tt}:=
	foralli(A:type)(eqA: Fun(a b: A).bool)
				 (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
				 (l1 l2 l3: <list A>)(u:{(list_seteq eqA l1 l2) = tt})
				 (v:{(list_seteq eqA l2 l3) = tt})(w:Forall(a:A).{(eqA a a) = tt})
				 (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
	   case terminates (list_subset A eqA l1 l3) by list_subset_total by lsp lst with
		  ff => contra
			
		   abbrev U1 = hypjoin (list_subset A eqA l1 l2) tt by [equal_to_subset A eqA eqA_total l1 l2 u] end in
		   abbrev U2 = hypjoin (list_subset A eqA l2 l3) tt by [equal_to_subset A eqA eqA_total l2 l3 v] end in	

			trans symm [list_transitivity A eqA eqA_total l1 l2 l3 U1 U2 w eqA_to_equals]
			trans hypjoin (list_subset A eqA l1 l3) ff by lsp end
			clash ff tt
			{ (list_seteq eqA l1 l3) = tt}
		| tt => case terminates (list_subset A eqA l3 l1) by list_subset_total by lsp2 lst2 with
			   ff => contra
				    abbrev v' = hypjoin (list_seteq eqA l3 l2) tt by 
					[list_seteq_symm A eqA eqA_total l2 l3 v ] end in 

				    abbrev V1 = hypjoin (list_subset A eqA l3 l2) tt by 
					[equal_to_subset A eqA eqA_total l3 l2 v'] end in

				   abbrev u' = hypjoin (list_seteq eqA l2 l1) tt by
				       [list_seteq_symm A eqA eqA_total l1 l2 u] end in					

				    abbrev V2 = hypjoin (list_subset A eqA l2 l1) tt by 
					[equal_to_subset A eqA eqA_total l2 l1 u'] end in
			
				    trans symm [list_transitivity A eqA eqA_total l3 l2 l1 V1 V2 w eqA_to_equals]

				    trans hypjoin  (list_subset eqA l3 l1) ff by lsp2 end
				clash ff tt
				{ (list_seteq eqA l1 l3) = tt}
				 
			 | tt => hypjoin (list_seteq A eqA l1 l3) tt by lsp lsp2 end
			 end
		end.
		



Define  list_subset_cons_tt_member :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (a:A)(l1 l2:<list A>)
        (u:{ (list_subset eqA (cons a l1) l2) = tt })
	(v:Forall(a:A).{(eqA a a) = tt})
	(eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
        { (member a l2 eqA) = tt } :=

  	    foralli(A:type)(eqA:Fun(a b: A).bool)(eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        	   (a:A)(l1 l2:<list A>)(u:{ (list_subset eqA (cons a l1) l2) = tt })
		   (v:Forall(a:A).{(eqA a a) = tt})
		   (eqA_to_equals: Forall(a b:A)(k:{(eqA a b) = tt}).{ a = b}).
	
	abbrev u' = hypjoin (member A a (cons a l1) eqA) tt by [v a] end in
	[member_trans_lemma A a eqA eqA_total (cons A a l1) l2 u' u eqA_to_equals]
  	
.
%-
Define trusted list_subset_cons_tt_subset :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        %maybe (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (a:A)(l1 l2:clause)
        (u:{ (list_subset eqA (cons a l1) l2) = tt }).
    { (list_subset eqA l1 l2) = tt }
  :=
  truei.


% may require the lemmas above
Define trusted list_subset_tt_subset_append:
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        %maybe (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2 l3:<list A>)
        (u:{ (list_subset A eqA l1 l2) = tt }).
    { (list_subset eqA l1 (append l2 l3)) = tt }
  :=
  truei.

Define trusted list_subset_tt_subset_cons :
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        %maybe (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (a:A)(l1 l2:clause)
        (u:{ (list_subset eqA l1 l2) = tt }).
    { (list_subset eqA l1 (cons a l2)) = tt }
  :=
  truei.

Define trusted list_subset_tt_subset_append_front:
  Forall(A:type)
        (eqA:Fun(a b: A).bool)
        %maybe (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (l1 l2 l3:<list A>)
        (u:{ (list_subset A eqA l1 l2) = tt }).
    { (list_subset eqA l1 (append l3 l2)) = tt }
  :=
  truei.
