Include "nat.g".
Include "owned.g".


Inductive ulist : Fun(A:type).type :=
  unil : Fun(spec A:type).<ulist A>
| ucons : Fun(spec A:type)(#untracked a:A)(l:<ulist A>). <ulist A>.

Define ufoldr : Fun(A B C: type)(^#owned cookie:C)
                  (fcn: Fun(^#owned cookie:C)(#untracked x:A)(y:B).B)
                  (b:B)(^#owned l : <ulist A>).B :=
  fun foldr(A B C: type)(^#owned cookie:C)
           (fcn: Fun(^#owned cookie:C)(#untracked x:A)(y:B).B)
           (b:B)(^#owned l : <ulist A>):B.
    match ! l with
      unil A' => b
   | ucons A' a' l' => 
     (fcn cookie a' (foldr A B C (clone_owned C cookie) fcn b l'))
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
        unil _ => existsi b {(ufoldr cookie f b l) = *}
                   hypjoin (ufoldr cookie f b l) b by u end
      | ucons _ a' l' => existse [IH l']
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
                    (^#owned l1 l2:<ulist A>)
                    .bool :=
  fun equlist(A:type)(eqA:Fun(#untracked x1 x2:A).bool)(^#owned l1 l2:<ulist A>):bool.
  match ! l1 with
    unil _ =>
      match ! l2 with
        unil _ => tt
      | ucons _ h2 t2 => ff
      end
  | ucons _ h1 t1 =>
      match ! l2 with
        unil _ => ff
      | ucons _ h2 t2 => 
         match (eqA h1 h2) with
           ff => ff
         | tt => (equlist A eqA t1 t2)
         end
      end
  end.

Define equlist_total
 : Forall(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
         (l1 l2:<ulist A>).
      Exists(o:bool).{ (equlist eqA l1 l2) = o } := 
	 foralli(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
    induction(l1:<ulist A>) by u v IH
      return Forall(l2:<ulist A>).Exists(o:bool).{ (equlist eqA l1 l2) = o } with
         unil _ => foralli(l2:<ulist A>).
			case l2 with
			  unil _ => existsi tt { (equlist eqA l1 l2) = * } 
						hypjoin (equlist eqA l1 l2) tt by u l2_eq end
			| ucons _ h2 t2  => existsi ff { (equlist eqA l1 l2) = * } 
						hypjoin (equlist eqA l1 l2) ff by u l2_eq end
			end

	| ucons _ h1 t1 => foralli(l2:<ulist A>).
			     case l2 with
			        unil _ => existsi ff { (equlist eqA l1 l2 ) = * } 
						hypjoin (equlist eqA l1 l2) ff by u l2_eq end
			       | ucons _ h2 t2 => 
				    case terminates (eqA h1 h2) by [eqA_total h1 h2] by g _ with
           				ff => existsi ff { (equlist eqA l1 l2) = * } 
						hypjoin (equlist eqA l1 l2) ff by u l2_eq g end
         				| tt => existsi terminates (equlist A eqA t1 t2) by [IH  t1 t2] 
							{ (equlist eqA l1 l2 ) = *} 
							hypjoin (equlist eqA l1 l2) 
							terminates (equlist eqA t1 t2) by [IH  t1 t2] 
							      by u l2_eq g end
					end
         							
			        end
	end.

Define trusted equlistEq
 : Forall(A:type)
         (l1 l2:<ulist A>)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
         (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
         (u:{ (equlist eqA l1 l2) = tt }).
       { l1 = l2 } :=
  truei.

Define ulist_mem : Fun(A:type)(eqA:Fun(#untracked a b:A).bool)(#untracked a:A)(l:<ulist A>).bool :=
  fun ulist_mem(A:type)(eqA:Fun(#untracked a b:A).bool)(#untracked a:A)(l:<ulist A>):bool.
    match l with
      unil _ => ff
    | ucons _ a' l' => match (eqA a a') with
                        ff => (ulist_mem A eqA a l')
                      | tt => do (dec <ulist A> l') tt end
                      end
    end.

Define ulist_isnil :=
	fun(A:type)(l:<ulist A>). 
	match l with
		unil A' => tt
	|	ucons A' a' l' => 
		do
			(dec <ulist A> l')
			ff
		end
	end.
