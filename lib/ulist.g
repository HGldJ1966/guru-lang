Include "unit.g".

Inductive ulist : Fun(A:type).type :=
  unil : Fun(spec A:type).<ulist A>
| ucons : Fun(spec A:type)(#untracked a:A)(l:<ulist A>). <ulist A>.

Define ufoldr : Fun(A B C: type)(^#owned cookie:C)
                  (fcn: Fun(^#owned cookie:C)(#untracked x:A)(y:B).B)
                  (b:B)(^#owned l : <ulist A>).B :=
  fun foldr(A B C: type)(^#owned cookie:C)
           (fcn: Fun(^#owned cookie:C)(#untracked x:A)(y:B).B)
           (b:B)(^#owned l : <ulist A>):B.
    match l with
      unil A' => do (consume_owned C cookie) b end
   | ucons A' a' l' => (fcn cookie a' 
                         (foldr A B C (clone_owned C cookie) fcn b l'))
   end. 

Define ufoldrTot : Forall(A B C : type)
                        (cookie:C)(f:Fun(cookie:C)(x:A)(y:B).B)
                        (fTot:Forall(x:A)(y:B).Exists(z:B).
                                 {(f cookie x y) = z})
                        (b:B)(l:<ulist A>).
                        Exists(z:B). {(ufoldr cookie f b l) = z } :=
  foralli(A B C : type)(cookie:C)(f:Fun(cookie:C)(x:A)(y:B).B)
         (fTot:Forall(x:A)(y:B).Exists(z:B).{(f cookie x y) = z})(b:B).
    induction(l:<ulist A>) by u v IH 
      return Exists(z:B). {(ufoldr cookie f b l) = z } with
        nil A' => existsi b {(ufoldr cookie f b l) = *}
                   hypjoin (ufoldr cookie f b l) b by u end
      | cons _ a' l' => existse [IH l']
                         foralli(z:B)(u1:{(ufoldr cookie f b l') = z}).
                           existse [fTot a' z]
                           foralli(z':B)(u2:{(f cookie a' z) = z'}).
                             existsi z' {(ufoldr cookie f b l) = *}
                               trans hypjoin 
                                       (ufoldr cookie f b l)
                                       (f cookie a' (ufoldr cookie f b l'))
                                      by u end
                               trans cong (f cookie a' *) u1
                                     u2
      end.

Define uappend_h := 
  fun(spec A:type)(^#owned cookie:nat)(#untracked x:A)(l:<ulist A>). (ucons A x l).

Define uappend : Fun(A : type)(^#owned l1:<ulist A>)(l2: <ulist A>).<ulist A> :=
  fun(A : type)(^#owned l1:<ulist A>)(l2: <ulist A>) : <ulist A>.
    let cookie = Z in 
    let ret = (ufoldr A <ulist A> nat (inspect nat cookie) (uappend_h A) l2 l1) in
    do (dec nat cookie)
       ret
    end.

Define equlist : Fun(A:type)(eqA:Fun(#untracked x1 x2:A).bool)
                    (^#owned l1 l2:<list A>)
                    .bool :=
  fun equlist(A:type)(eqA:Fun(#untracked x1 x2:A).bool)(^#owned l1 l2:<list A>):bool.
  match l1 with
    nil _ =>
      match l2 with
        nil _ => tt
      | cons _ h2 t2 => ff
      end
  | cons _ h1 t1 =>
      match l2 with
        nil _ => ff
      | cons _ h2 t2 => 
         match (eqA h1 h2) with
           ff => ff
         | tt => (equlist A eqA t1 t2)
         end
      end
  end.

Define trusted equlist_total
 : Forall(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
         (l1 l2:<ulist A>).
      Exists(o:bool).{ (equlist eqA l1 l2) = o } := truei.

Define trusted equlistEq
 : Forall(A:type)
         (l1 l2:<ulist A>)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
         (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
         (u:{ (equlist eqA l1 l2) = tt }).
       { l1 = l2 } :=
  truei.