Unset "check_drop_annos_idem".
Include "nat.g".
Include "minus.g".

%Set "print_parsed".

Inductive list : Fun(A:type).type :=
  nil : Fun(A:type).<list A>
| cons : Fun(A:type)(a:A)(l:<list A>). <list A>.


Define hd := fun(A:type)(owned l:<list A>).
  match l by x y return A with
    nil A' => abort A
  | cons A' a' l' => cast inc a' by symm inj <list *> y end.

Define tl := fun(A:type)(l:<list A>).
  match l by x y return <list A> with
    nil A' => abort <list A>
  | cons A' a' l' => cast l' by symm y end.

%- this is the same as fold except with a different name and the Haskell
   order of arguments. -%
Define foldr : Fun(A B: type)(fcn: Fun(owned x:A)(y:B).B)(b:B)(owned l : <list A>).B :=
	fun foldr(A B: type)(fcn: Fun(owned x:A)(y:B).B)(b:B)(owned l: <list A>) : B.
	match l by u v return B with
		  nil A' => b
		| cons A' a' l' => (fcn cast a' by symm inj <list *> v
                                      (foldr A B fcn b cast l' by cong <list *> symm inj <list *> v))
end.

Define foldrTot : Forall(A B : type)(f:Fun(owned x:A)(y:B).B)
                        (fTot:Forall(x:A)(y:B).Exists(z:B).{(f x y) = z})
                        (b:B)(l:<list A>).
                        Exists(z:B). {(foldr ! ! f b l) = z } :=
  foralli(A B : type)(f:Fun(owned x:A)(y:B).B)
         (fTot:Forall(x:A)(y:B).Exists(z:B).{(f x y) = z})(b:B).
    induction(l:<list A>) by u v IH 
      return Exists(z:B). {(foldr ! ! f b l) = z } with
        nil A' => existsi b {(foldr ! ! f b l) = *}
                   hypjoin (foldr ! ! f b l) b by u end
      | cons A' a' l' => existse [IH cast l' by symm v]
                         foralli(z:B)(u1:{(foldr ! ! f b l') = z}).
                           existse [fTot cast a' by symm inj <list *> v z]
                           foralli(z':B)(u2:{(f a' z) = z'}).
                             existsi z' {(foldr ! ! f b l) = *}
                               trans hypjoin (foldr ! ! f b l)
                                     (f a' (foldr ! ! f b l')) by u end
                               trans cong (f a' *) u1
                                     u2
      end.

Define foldl : Fun(A B: type)(fcn: Fun(x:A)(y:B).B)(b:B)(l : <list A>).B :=
	fun foldl(A B: type)(fcn: Fun(x:A)(y:B).B)(b:B)(l: <list A>) : B.
	match l by u v return B with 
		  nil A' => b
		| cons A' a' l' => (foldl A B fcn (fcn cast a' by symm inj <list *> v b) cast l' by cong <list *> symm inj <list *> v)
	end.

Define foldl1 : Fun (A : type)(fcn: Fun(x:A)(y:A).A)(l : <list A>).A :=
	fun foldl1(A : type)(fcn: Fun(x:A)(y:A).A)(l : <list A>) : A.
	 match l by u v return A with
		nil A' =>  abort A 
		| cons A' a' l' => (foldl A A fcn cast a' by symm inj <list *> v cast l' by cong <list *> symm inj <list *> v)
	end.

Define map : Fun(A B: type)(l : <list A>)(fcn: Fun(owned a:A).B).<list B> :=
	fun map (A B: type)(l : <list A>)(fcn: Fun(owned a:A).B) : <list B>.
	(foldr A <list B> fun(owned a:A)(l': <list B>).(cons B (fcn a) l') (nil B) l).

Define mk_list := fun mk_list(A:type)(a:A)(n:nat):<list A>.
                    match n with
                      Z => (nil A)
                    | S n' => (cons A a (mk_list A a n'))
                  end.

% Set "comment_vars".

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


Include "bool.g".
Include "nat.g".
Include "plus.g".
Include "minmax.g".

Define filter :=
  fun (A: type)(owned l : <list A>)(fcn: Fun(owned a:A).bool).
  (foldr A <list A> fun(owned a:A)(l:<list A>).
                      match (fcn a) with ff => l | tt => (cons A inc a l) end
     (nil A) l).

Define filter_skip 
  : Forall(A:type)(a:A)(l:<list A>)(fcn:Fun(a:A).bool)
          (u:{(fcn a) = ff}). 
          { (filter ! (cons ! a l) fcn) = (filter ! l fcn) } :=
  foralli(A:type)(a:A)(l:<list A>)(fcn:Fun(a:A).bool)
         (u:{(fcn a) = ff}).
    eabbrev fl = (filter ! l fcn) in
    trans join (filter ! (cons ! a l) fcn)
               match (fcn a) with ff => fl | tt => (cons ! a fl) end
    trans cong match * with ff => fl | tt => (cons ! a fl) end u
          join match ff with ff => fl | tt => (cons ! a fl) end
               (filter ! l fcn).

Define filter_tot :=
  foralli(A: type)(l : <list A>)(fcn: Fun(owned a:A).bool)
         (fcnTot:Forall(x:A).Exists(z:bool).{(fcn x) = z}).
   abbrev F = fun(owned a:A)(l:<list A>).
                 match (fcn a) with ff => l | tt => (cons A a l) end in
   existse
   [foldrTot A <list A> F 
      foralli(a:A)(l:<list A>).
        existse [fcnTot a] 
        induction(b:bool) by ub ign ign 
        return Forall(u:{(fcn a) = b}). Exists(r:<list A>).
               { (F a l) = r } with
          ff => foralli(u:{(fcn a) = b}).
                existsi l { (F a l) = * } 
                  hypjoin (F a l) l by trans u ub end
        | tt => foralli(u:{(fcn a) = b}).
                existsi (cons A a l) { (F a l) = * } 
                  hypjoin (F a l) (cons A a l) by trans u ub end
        end (nil A) l]
   foralli(r:<list A>)(u:{(foldr A <list A> F (nil A) l) = r}).
   existsi r {(filter A l fcn) = *}
     trans join (filter A l fcn) (foldr A <list A> F (nil A) l)
           u.          

Define length : Fun(A: type)(owned l : <list A>).nat :=
	fun length (A: type)(owned l : <list A>) : nat.
	(foldr A nat fun(owned a:A)(b:nat).(S b) Z l). 

Define length_tot 
  : Forall(A: type)(l : <list A>).Exists(n:nat). {(length A l) = n} :=
  foralli(A: type)(l : <list A>).
    existse 
      [foldrTot A nat fun(owned a:A)(b:nat).(S b) 
       foralli(a:A)(b:nat).existsi (S b) { (fun(owned a:A)(b:nat).(S b) a b) = *}
                           join (fun(owned a:A)(b:nat).(S b) a b) (S b)
       Z l]
    foralli(n:nat)(u:{(foldr A nat fun(owned a:A)(b:nat).(S b) Z l) = n}).
    existsi n {(length A l) = *}
      trans join (length A l)
                 (foldr A nat fun(owned a:A)(b:nat).(S b) Z l)
            u.


Define maximum : Fun(l : <list nat>).nat :=
	fun maximum (l : <list nat>) : nat.
	(foldl1 nat max l).

Define minimum : Fun(l : <list nat>).nat :=
	fun maximum (l : <list nat>) : nat.
	(foldl1 nat min l).

Define any : Fun (A : type)(l : <list A>)(fcn: Fun(x:A).bool).bool :=
	fun any(A : type)(l: <list A>)(fcn: Fun(x:A).bool) : bool. 
	(foldr A bool fun(owned a:A)(b:bool).(or (fcn a) b) ff l).

Define all : Fun (A : type)(l : <list A>)(fcn: Fun(x:A).bool).bool :=
	fun all (A : type)(l : <list A>)(fcn: Fun(x:A).bool) : bool.
	(foldr A bool fun(owned a:A)(b:bool).(and (fcn a) b) tt l).

%- This is append, written with fold, can likely replace append -%
Define appendf : Fun(A : type)(owned l1:<list A>)(l2: <list A>).<list A> :=
	fun appendf(A : type)(owned l1:<list A>)(l2: <list A>) : <list A>.
	(foldr A <list A> fun(owned x:A).(cons A inc x) l2 l1).

%- We should rename appendf to append and get rid of the old append. -%
Define foldr_appendf : Forall(A B : type)(f:Fun(owned a:A)(b:B).B)(b:B)
                             (l1 l2:<list A>).
                       {(foldr ! ! f b (appendf ! l1 l2)) = (foldr ! ! f (foldr ! ! f b l2) l1)} :=
  foralli(A B:type)(f:Fun(owned a:A)(b:B).B)(b:B).
    induction(l1:<list A>) by u v IH 
    return Forall(l2:<list A>).
           {(foldr ! ! f b (appendf ! l1 l2)) = (foldr ! ! f (foldr ! ! f b l2) l1)} with
      nil A' => foralli(l2:<list A>).
                  trans cong (foldr ! ! f b (appendf ! * l2)) u
                  trans join (foldr ! ! f b (appendf ! (nil !) l2))
                             (foldr ! ! f (foldr ! ! f b l2) (nil !))
                        cong (foldr ! ! f (foldr ! ! f b l2) *) symm u
   | cons A' a' l1' => 
       foralli(l2:<list A>).
        trans cong (foldr ! ! f b (appendf ! * l2)) u
        trans join (foldr ! ! f b (appendf ! (cons ! a' l1') l2))
                   (f a' (foldr ! ! f b (appendf ! l1' l2)))
        trans cong (f a' *) [IH cast l1' by symm v l2]
        trans join (f a' (foldr ! ! f (foldr ! ! f b l2) l1'))
                   (foldr ! ! f (foldr ! ! f b l2) (cons ! a' l1'))
              cong (foldr ! ! f (foldr ! ! f b l2) *) symm u
   end.

Define appendfTot : Forall(A : type)(l1 l2: <list A>).Exists(l : <list A>).
                      { (appendf A l1 l2) = l } :=
  foralli(A : type)(l1 l2: <list A>).
  existse [foldrTot A <list A> fun(owned x:A).(cons A inc x) 
             foralli(x:A)(l:<list A>).
               existsi (cons A x l) { (fun(owned x:A).(cons A inc x) x l) = * }
                 join (fun(owned x:A).(cons A inc x) x l) (cons A x l)
             l2 l1] 
  foralli(z:<list A>)(u:{(foldr fun(owned x:!).(cons x) l2 l1) = z}).
    existsi z {(appendf A l1 l2) = *}
      trans join (appendf A l1 l2) (foldr fun(owned x:!).(cons x) l2 l1)
            u.

Define appendf_eq_nil1 : Forall(A:type)(l1 l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}).
                         { l1 = (nil !) } :=
  foralli(A:type).
  induction(l1:<list A>) by u v IH return Forall(l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}).
                         { l1 = (nil !) } with
    nil A' => foralli(l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}). u
  | cons A' x' l1' => foralli(l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}).
                        abbrev p = 
                           trans symm U
                           trans cong (appendf ! * l2) u
                                 join (appendf ! (cons ! x' l1') l2)
                                      (cons ! x' (appendf ! l1' l2)) in 
                        existse cinv
                                     (appendf A cast l1' by symm v l2)
                                     trans cong (cons x' *) symm eval (appendf l1' l2) symm p
                        foralli(z:<list A>)(V:{(appendf ! l1' l2) = z}).
                           contra
                             trans p 
                             trans cong (cons ! x' *) V
                                   clash (cons ! x' z) (nil !)
                           { l1 = (nil !) } 
  end.

Define appendf_eq_nil2 : Forall(A:type)(l1 l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}).
                         { l2 = (nil !) } :=
  foralli(A:type)(l1 l2:<list A>)(U:{(appendf ! l1 l2) = (nil !)}).
    symm
      trans symm U
      trans cong (appendf ! * l2) [appendf_eq_nil1 A l1 l2 U]
            join (appendf ! (nil !) l2)
                 l2.

Define appendf_assoc : Forall(A:type)(l1 l2 l3:<list A>).
                       { (appendf ! (appendf ! l1 l2) l3) = (appendf ! l1 (appendf ! l2 l3)) } :=
  foralli(A:type)(l1 l2 l3:<list A>).
    trans join (appendf (appendf l1 l2) l3)
               (foldr fun(owned x:!).(cons x) l3 (appendf l1 l2))
    trans [foldr_appendf A <list A> fun(owned x:A).(cons A x) l3 l1 l2]
          join (foldr fun(owned x:!).(cons x) (foldr fun(owned x:!). (cons x) l3 l2) l1)
               (appendf l1 (appendf l2 l3)).

Define appendf_nil0 : Forall(A:type)(l:<list A>).{ (appendf ! l (nil !)) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (appendf ! l (nil !)) = l } with
      nil A' =>
        hypjoin (appendf ! l (nil !))
                l
             by lp end
    | cons A' h t =>
        trans hypjoin (appendf ! l (nil !))
                      (cons ! h (appendf ! t (nil !)))
                   by lp end
        trans cong (cons ! h *)
                   [IHl cast t by cong <list *> symm inj <list *> lt]
              symm lp
    end.

Define appendf_nil1 : Forall(A:type)(l1: <list A>).{(appendf ! (nil !) l1) = l1} :=
	foralli(A:type).induction(l1:<list A>) by p t IH return
		{(appendf ! (nil !) l1) = l1} with
	nil A' =>
		trans cong (appendf ! (nil !) *) p
		trans join (appendf ! (nil !) (nil !))
			   (nil !)
		symm p
	| cons A' a' l1' =>
		trans cong (appendf ! (nil !) *) p
		trans join (appendf ! (nil !) (cons ! a' l1'))
			   (foldr ! ! (cons !) (cons ! a' l1') (nil !))
		trans join (foldr ! ! (cons !) (cons ! a' l1') (nil !))
			   (cons ! a' l1')
		symm p
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

Define nth : Fun(A:type)(n:nat)(l:<list A>).A :=
  fun (A:type). fun nth(n:nat)(l:<list A>):A.
     match l by x y return A with
       nil A' => abort A
     | cons A' a' l' =>
         match n return A with
           Z => cast a' by symm inj <list *> y
         | S n' => (nth n' cast l' by symm y)
         end
     end.

Define update : Fun(A:type)(n:nat)(a:A)(l:<list A>).<list A> :=
    fun update(A:type)(n:nat)(a:A)(l:<list A>):<list A>.
      match l by ul vl with 
        nil A' => abort <list A>
      | cons A' a' l' => match n with
                           Z => (cons A a cast l' by symm vl)
                         | S n' => (cons A cast a' by symm inj <list *> vl
                                      (update A n' a l))
                         end
      end.

Define concat : Fun(A:type)(l:<list <list A>>).<list A> :=
 fun concat(A:type)(l:<list <list A>>):<list A>.
 (foldr  <list A> <list A> (appendf A) (nil A) l). 

%-
Define concatTot : Forall(A:type)(l:<list <list A>>).Exists(l':<list A>). 
                     { (concat A l) = l' } :=
  (appendf A)
  [foldrTot <list A> <list A>  
-%

%-
Define concat_app : Forall(A:type)(l1 l2:<list  <list A>>).
                     { (appendf ! (concat ! l1)(concat ! l2)) = (concat ! (appendf ! l1 l2)) } :=
    foralli(A: type)(l1 l2:<list <list A>>).
        induction(l1:<list <list A>>) by lp lt IH return Forall(l2:<list<list A>>).
		{ (appendf ! (concat ! l1)(concat ! l2)) = (concat ! (appendf ! l1 l2)) } with
	nil A' => foralli(l2:<list <list A>>).
		trans cong (appendf ! (concat ! *) (concat ! l2)) lp
		trans join (appendf ! (concat ! (nil !)) (concat ! l2))
			   (appendf ! (nil !) (concat ! l2))
		trans join (appendf ! (nil !) (concat ! l2))
			   (concat ! l2)
		symm lp
	| cons A' a' l1' => foralli(l2: <list <list A>>).
		trans cong (appendf ! (concat ! *) (concat ! l2)) lp
		trans join (appendf ! (concat ! (cons ! a' l1')) (concat ! l2))
			   (appendf ! (foldr !! (appendf !) (nil !) (cons ! a' l1')) (concat ! l2))
		trans join (appendf ! (foldr !! (appendf !) (nil !) (cons ! a' l1')) (concat ! l2))
			   (appendf ! (appendf ! a' (foldr !! (appendf !) (nil !) l1')) (concat ! l2))
		trans join (appendf ! (appendf ! a' (foldr !! (appendf !) (nil !) l1')) (concat ! l2))
			   (appendf ! (appendf ! a' (concat ! l1')) (concat ! l2))
		trans join (appendf ! (appendf ! a' (concat ! l1')) (concat ! l2))
			   (foldr !! (cons !) (concat ! l2) (appendf ! a' (concat ! l1')))
		trans [foldr_appendf ! ! (cons !) (concat ! l2) a' (concat ! l1')] %% Error line - Expected an Inactive Expression
			join (foldr !! (cons !) (concat ! l2) (appendf ! a' (concat ! l1')))
			     (foldr !! (cons !) (foldr !! (cons !) (concat ! l2) (concat ! l1')) a')
		trans join (foldr !! (cons !) (foldr !! (cons !) (concat ! l2) (concat ! l1')) a')
			   (foldr !! (cons!) (appendf ! (concat ! l1') (concat ! l2)) a')
		trans cong (foldr !! (cons!) * a') [IH cast l1' by symm v l2]
		trans join (foldr !! (cons!) (concat ! (appendf ! l1' l2)) a')
			   (appendf ! a' (concat ! (appendf ! l1' l2)))
		trans join (appendf ! a' (concat ! (appendf ! l1' l2)))
			   (appendf ! a' (foldr !! (appendf !) (nil !) (appendf ! l1' l2)))
		trans join (appendf ! a' (foldr !! (appendf !) (nil !) (appendf ! l1' l2)))
			   (foldr !! (appendf !) (nil !) (cons ! a' (appendf ! l1' l2)))
		trans join (foldr !! (appendf !) (nil !) (cons ! a' (appendf ! l1' l2)))
			   (concat ! (cons ! a' (appendf ! l1' l2)))
		trans join (concat ! (cons ! a' (appendf ! l1' l2)))
			   (concat ! (cons ! a' (foldr !! (cons !) l2 l1')))
		trans join (concat ! (cons ! a' (foldr !! (cons !) l2 l1')))
			   (concat ! (foldr !! (cons !) l2 (cons ! a' l1')))
		trans join (concat ! (foldr !! (cons !) l2 (cons ! a' l1')))
			   (concat ! (appendf ! (cons ! a' l1') l2))
		symm lp	   
end.
-%

Define list_length : Fun(A:type)(l:<list A>).nat :=
  fun list_length(A:type)(l:<list A>):nat.
  match l by lp lt return nat with
    nil A' => Z
  | cons A' h t => (S (list_length A cast t by cong <list *> symm inj <list *> lt))
  end.

Define list_length_total : Forall(A:type)(l:<list A>).Exists(n:nat).{ (list_length A l) = n } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Exists(n:nat).{ (list_length A l) = n } with
      nil A' =>
        existsi Z { (list_length A l) = * }
          trans cong (list_length A *) lp
                join (list_length A (nil A)) Z
    | cons A' h t =>
        existse [IHl cast t by cong <list *> symm inj <list *> lt]
          foralli(n':nat)(u:{ (list_length A t) = n' }).
            existsi (S n') { (list_length A l) = * }
              trans cong (list_length A *) lp
              trans join (list_length A (cons A h t)) (S (list_length A t))
                    cong (S *) u
    end.

Define list_length_nonzero_implies_nonnil : Forall(A:type)(l:<list A>)(u:{ (list_length ! l) != Z }).{ l != (nil !) } :=
  % proof is by contradiction
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(u:{ (list_length ! l) != Z }).{ l != (nil !) } with
      nil A' =>
        foralli(u:{ (list_length ! l) != Z }).
          contra trans join Z (list_length ! (nil !))
                 trans cong (list_length ! *) symm lp
                       u
            { l != (nil !) }
    | cons A' h t =>
        foralli(u:{ (list_length ! l) != Z }).
          trans lp
                clash (cons ! h t) (nil !)
    end.

%-
Define list_to_listn : Fun(A:type)(l:<list A>).<listn A (list_length A l)> :=
  fun list_to_listn(A:type)(l:<list A>):<listn A (list_length A l)>.
  match l by lp lt return <listn A (list_length A l)> with
    nil A' => cast (niln A) by
                cong <listn A *>
                     trans join Z (list_length A (nil A))
                           cong (list_length A *) symm lp
  | cons A' h t =>
      abbrev h' = cast h by symm inj <list *> lt in
      abbrev t' = cast t by cong <list *> symm inj <list *> lt in
      cast (consn A (list_length A t') h' (list_to_listn A t')) by
        cong <listn A *>
             trans join (S (list_length A t'))
                        (list_length A (cons A h t))
                   cong (list_length A *) symm lp
  end.

Define listn_to_list : Fun(A:type)(n:nat)(l:<listn A n>).<list A> :=
  fun listn_to_list(A:type)(n:nat)(l:<listn A n>):<list A>.
  match l by lp lt return <list A> with
    niln A' =>
      (nil A)
  | consn A' n' h t =>
      (cons A cast h by symm inj <listn * **> lt (listn_to_list A n' cast t by cong <listn * n'> symm inj <listn * **> lt))
  end.

Define list_listn_same : Forall(A:type)(l:<list A>).{ (listn_to_list A (list_length A l) (list_to_listn A l)) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (listn_to_list A (list_length A l) (list_to_listn A l)) = l } with
      nil A' =>
        trans cong (listn_to_list A (list_length A l) *)
                   trans cong (list_to_listn A *) lp
                         join (list_to_listn A (nil A)) (niln A)
        trans cong (listn_to_list A * (niln A))
                   trans cong (list_length A *) lp
                         join (list_length A (nil A)) Z
        trans join (listn_to_list A Z (niln A))
                   (nil A)
              symm lp
    | cons A' h t =>
        existse [list_length_total A cast t by cong <list *> symm inj <list *> lt]
          foralli(n:nat).
            foralli(u:{ (list_length A t) = n }).
              trans cong (listn_to_list A (list_length A *) (list_to_listn A *)) lp
              trans join (listn_to_list A (list_length A (cons A h t)) (list_to_listn A (cons A h t)))
                         (cons A h (listn_to_list A (list_length A t) (list_to_listn A t)))
              trans cong (cons A h *)
                         [IHl cast t by cong <list *> symm inj <list *> lt]
                    symm lp
    end.

Define list_length_listn : Forall(A:type)(n:nat)(l:<listn A n>).{ (list_length A (listn_to_list A n l)) = n } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<listn A n>).{ (list_length A (listn_to_list A n l)) = n } with
      Z =>
        induction(l:<listn A n>) by lp lt IHl return { (list_length A (listn_to_list A n l)) = n } with
          niln A' =>
            trans cong (list_length A *)
                       trans cong (listn_to_list A n *) lp
                       trans cong (listn_to_list A * (niln A)) np
                             join (listn_to_list A Z (niln A)) (nil A)
            trans join (list_length A (nil A)) Z
                  symm np
        | consn A' n'' h t =>
            contra trans inj <listn ** *>
                             trans cong <listn A *> symm np
                                   lt
                         clash (S n'') Z
                   { (list_length A (listn_to_list A n l)) = n }
        end
    | S n' =>
        induction(l:<listn A n>) by lp lt IHl return { (list_length A (listn_to_list A n l)) = n } with
          niln A' =>
            contra trans inj <listn ** *>
                             trans symm lt
                                   cong <listn A *> np
                         clash (S n') Z
                   { (list_length A (listn_to_list A n l)) = n }
        | consn A' n'' h t =>
            trans cong (list_length A (listn_to_list A n *)) lp
            trans cong (list_length A (listn_to_list A * (consn A n'' h t))) np
            trans join (list_length A (listn_to_list A (S n') (consn A n'' h t)))
                       (S (list_length A (listn_to_list A n' t)))
            trans cong (S *) [IHn n' cast t by trans cong <listn * n''> symm inj <listn * **> lt cong <listn A *> inj (S *) trans symm inj <listn ** *> lt np]
                  symm np
        end
    end.

% there is a lot of redundant code here -- the breakouts might be necessary?!  think about this..
Define listn_list_same : Forall(A:type)(n:nat)(l:<listn A n>).{ (list_to_listn A (listn_to_list A n l)) = l } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<listn A n>).{ (list_to_listn A (listn_to_list A n l)) = l } with
      Z =>
        induction(l:<listn A n>) by lp lt IHl return { (list_to_listn A (listn_to_list A n l)) = l } with
          niln A' =>
            trans cong (list_to_listn A (listn_to_list A n *)) lp
            trans join (list_to_listn A (listn_to_list A n (niln A)))
                       (niln A)
                  symm lp
        | consn A' n' h t =>
            %% this breakout is probably not necessary
            [ induction(n'':nat) by n''p n''t IHn'' return Forall(u:{ n' = n'' }).{ (list_to_listn A (listn_to_list A n l)) = l } with
                Z =>
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A Z h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A Z t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A Z t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              | S n''' =>%% (consn A (list_length A (listn_to_list A Z t)) h t)
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A (S n''') h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A (S n''') t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A (S n''') t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              end n' join n' n' ]
        end
    | S npred =>
        induction(l:<listn A n>) by lp lt IHl return { (list_to_listn A (listn_to_list A n l)) = l } with
          niln A' =>
            trans cong (list_to_listn A (listn_to_list A n *)) lp
            trans join (list_to_listn A (listn_to_list A n (niln A)))
                       (niln A)
                  symm lp
        | consn A' n' h t =>
            %% this breakout is probably not necessary
            [ induction(n'':nat) by n''p n''t IHn'' return Forall(u:{ n' = n'' }).{ (list_to_listn A (listn_to_list A n l)) = l } with
                Z =>
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A Z h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A Z t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A Z t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              | S n''' =>%% (consn A (list_length A (listn_to_list A Z t)) h t)
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A (S n''') h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A (S n''') t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A (S n''') t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              end n' join n' n' ]
        end
    end.
-%

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

Define list_fstn : Fun(A:type)(l:<list A>)(n:nat).<list A> :=
  fun list_fstn(A:type)(l:<list A>)(n:nat):<list A>.
    match l by lp lt return <list A> with
      nil A' => (nil A)
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        match n by np nt return <list A> with
          Z => (nil A)
        | S n' => (cons A hcast (list_fstn A tcast n'))
        end
    end.

Define list_fstn_total : Forall(A:type)(l:<list A>)(n:nat).Exists(o:<list A>).{ (list_fstn ! l n) = o } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(n:nat).Exists(o:<list A>).{ (list_fstn ! l n) = o } with
      nil A' =>
        foralli(n:nat).
          existsi (nil A) { (list_fstn A l n) = * }
            trans cong (list_fstn ! * n) lp
                  join (list_fstn ! (nil !) n)
                       (nil !)
    | cons A' h t =>
        induction(n:nat) by np nt IHn return Exists(o:<list A>).{ (list_fstn A l n) = o } with
          Z =>
            existsi (nil A) { (list_fstn A l n) = * }
              trans cong (list_fstn ! * n) lp
              trans cong (list_fstn ! (cons ! h t) *) np
                    join (list_fstn ! (cons ! h t) Z)
                         (nil !)
        | S n' =>
            abbrev hcast = cast h by symm inj <list *> lt in
            abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
            existse [IHl tcast n']
              foralli(o':<list A>)(u:{ (list_fstn ! t n') = o' }).
                existsi (cons A hcast o') { (list_fstn ! l n) = * }
                  trans cong (list_fstn ! * n) lp
                  trans cong (list_fstn ! (cons ! h t) *) np
                  trans join (list_fstn ! (cons ! h t) (S n'))
                             (cons ! h (list_fstn ! t n'))
                        cong (cons ! h *) u
        end
    end.

Define list_fstn_ident : Forall(A:type)(l:<list A>).{ (list_fstn ! l (list_length ! l)) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (list_fstn ! l (list_length ! l)) = l } with
      nil A' =>
        trans cong (list_fstn ! * (list_length ! *)) lp
        trans join (list_fstn ! (nil !) (list_length ! (nil !)))
                   (nil !)
              symm lp
    | cons A' h t =>
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        trans cong (list_fstn ! * (list_length ! *)) lp
        trans join (list_fstn ! (cons ! h t) (list_length ! (cons ! h t)))
                   (cons ! h (list_fstn ! t (list_length ! t)))
        trans cong (cons ! h *)
                   [IHl tcast]
              symm lp
    end.

Define list_fstn_length : Forall(A:type)(l:<list A>)(n:nat).{ (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) (eqnat (list_length ! (list_fstn ! l n)) n)) = tt } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(n:nat).{ (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) (eqnat (list_length ! (list_fstn ! l n)) n)) = tt } with
      nil A' =>
        induction(n:nat) by np nt IHn return { (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) (eqnat (list_length ! (list_fstn ! l n)) n)) = tt } with
          Z =>
            symm trans symm [or_def2 terminates (eqnat terminates (list_length A terminates (list_fstn A l n) by list_fstn_total) by list_length_total
                                                       terminates (list_length A l) by list_length_total)
                                                by eqnatTot]
                       cong (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) *)
                            trans symm [x_eqnat_x n]
                                  cong (eqnat * n)
                                       symm trans cong (list_length ! *)
                                                  trans cong (list_fstn ! * n) lp
                                                        join (list_fstn ! (nil !) n)
                                                             (nil !)
                                            trans join (list_length ! (nil !))
                                                       Z
                                                  symm np
        | S n' =>
           symm trans join tt (or tt (eqnat (list_length ! (list_fstn ! l n)) n))
                      cong (or * (eqnat (list_length ! (list_fstn ! l n)) n))
                           trans symm [x_eqnat_x terminates (list_length A l) by list_length_total]
                                 cong (eqnat * (list_length ! l))
                                      symm trans cong (list_length ! *)
                                                 trans cong (list_fstn ! * n) lp
                                                       join (list_fstn ! (nil !) n)
                                                            (nil !)
                                                 cong (list_length ! *)
                                                      symm lp
        end
    | cons A' h t =>
        induction(n:nat) by np nt IHn return { (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) (eqnat (list_length ! (list_fstn ! l n)) n)) = tt } with
          Z =>
            symm trans symm [or_def2 terminates (eqnat terminates (list_length A terminates (list_fstn A l n) by list_fstn_total) by list_length_total
                                                       terminates (list_length A l) by list_length_total)
                                                by eqnatTot]
                       cong (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) *)
                            trans symm [x_eqnat_x n]
                                  cong (eqnat * n)
                                       symm trans cong (list_length ! *)
                                                  trans cong (list_fstn ! * n) lp
                                                  trans cong (list_fstn ! (cons ! h t) *) np
                                                        join (list_fstn ! (cons ! h t) Z)
                                                             (nil !)
                                            trans join (list_length ! (nil !))
                                                       Z
                                                  symm np
        | S n' =>
            abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
            existse [eqnatTot terminates (list_length A terminates (list_fstn A tcast n') by list_fstn_total) by list_length_total
                              terminates (list_length A tcast) by list_length_total]
              induction(o:bool) by op ot IHo return Forall(u:{ (eqnat (list_length ! (list_fstn ! t n')) (list_length ! t)) = o }).{ (or (eqnat (list_length ! (list_fstn ! l n)) (list_length ! l)) (eqnat (list_length ! (list_fstn ! l n)) n)) = tt } with
                ff =>
                  foralli(u:{ (eqnat (list_length ! (list_fstn ! t n')) (list_length ! t)) = o }).
                    symm trans symm [or_def2 terminates (eqnat terminates (list_length A terminates (list_fstn A l n) by list_fstn_total) by list_length_total
                                                               terminates (list_length A l) by list_length_total) by eqnatTot]
                               cong (or (eqnat (list_length A (list_fstn A l n)) (list_length A l)) *)
                                    trans symm [x_eqnat_x n]
                                          cong (eqnat * n)
                                               symm trans cong (list_length ! (list_fstn ! * n)) lp
                                                    trans cong (list_length ! (list_fstn ! (cons ! h t) *)) np
                                                    trans join (list_length ! (list_fstn ! (cons ! h t) (S n')))
                                                               (S (list_length ! (list_fstn ! t n')))
                                                    trans cong (S *)
                                                               [eqnatEq terminates (list_length A terminates (list_fstn A tcast n') by list_fstn_total) by list_length_total n'
                                                                        symm trans symm [IHl tcast n']
                                                                             trans cong (or * (eqnat (list_length ! (list_fstn ! t n')) n'))
                                                                                        trans u op
                                                                                   join (or ff (eqnat (list_length ! (list_fstn ! t n')) n'))
                                                                                        (eqnat (list_length ! (list_fstn ! t n')) n')]
                                                          symm np
              | tt =>
                  foralli(u:{ (eqnat (list_length ! (list_fstn ! t n')) (list_length ! t)) = o }).
                    symm trans join tt
                                    (or tt (eqnat (list_length ! (list_fstn ! l n)) n))
                               cong (or * (eqnat (list_length ! (list_fstn ! l n)) n))
                                    trans symm [x_eqnat_x terminates (list_length A l) by list_length_total]
                                          cong (eqnat * (list_length ! l))
                                               trans cong (list_length ! *) lp
                                               trans join (list_length ! (cons ! h t))
                                                          (S (list_length ! t))
                                               trans cong (S *)
                                                          symm [eqnatEq terminates (list_length A terminates (list_fstn A tcast n') by list_fstn_total) by list_length_total
                                                                        terminates (list_length A tcast) by list_length_total
                                                                        trans u op]
                                               trans join (S (list_length ! (list_fstn ! t n')))
                                                          (list_length ! (list_fstn ! (cons ! h t) (S n')))
                                               trans cong (list_length ! (list_fstn ! * (S n'))) symm lp
                                                     cong (list_length ! (list_fstn ! l *)) symm np
              end
        end
    end.

Define list_length_ne_list_ne : Forall(A:type)
                                      (l1 l2:<list A>)
                                      (u:{ (list_length ! l1) != (list_length ! l2) }).
                                  { l1 != l2 } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)(u:{ (list_length ! l1) != (list_length ! l2) }).{ l1 != l2 } with
      nil A1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(u:{ (list_length ! l1) != (list_length ! l2) }).{ l1 != l2 } with
          nil A2 =>
            foralli(u:{ (list_length ! l1) != (list_length ! l2) }).
              contra trans cong (list_length ! *)
                                trans l2p symm l1p
                           u
                { l1 != l2 }
        | cons A2 h2 t2 =>
            foralli(u:{ (list_length ! l1) != (list_length ! l2) }).
              trans l1p
                    symm trans l2p
                               clash (cons ! h2 t2)
                                     (nil !)
        end
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(u:{ (list_length ! l1) != (list_length ! l2) }).{ l1 != l2 } with
          nil A2 =>
            foralli(u:{ (list_length ! l1) != (list_length ! l2) }).
              trans l1p
                    symm trans l2p
                               clash (nil !)
                                     (cons ! h1 t1)
        | cons A2 h2 t2 =>
            foralli(u:{ (list_length ! l1) != (list_length ! l2) }).
              abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
              abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
              abbrev u' = [Sneq_neq terminates (list_length A t1cast) by list_length_total
                                    terminates (list_length A t2cast) by list_length_total
                                    symm trans symm trans cong (list_length ! *) l2p
                                                          join (list_length ! (cons ! h2 t2))
                                                               (S (list_length ! t2))
                                               symm trans symm trans cong (list_length ! *) l1p
                                                                          join (list_length ! (cons ! h1 t1))
                                                                               (S (list_length ! t1))
                                                          u] in
              symm trans l2p
                         symm trans l1p
                                    symm ncong (cons A ** *)
                                               (cons A h2 t2)
                                               (cons A h1 t1)
                                               symm [IHl1 t1cast t2cast u']
        end
    end.

Define list_not_length_1 : Forall(A:type)
                                 (h1 h2:A)
                                 (t:<list A>)
                                 (x:A).
                             { (cons ! h1 (cons ! h2 t)) != (cons ! x (nil !)) } :=
  foralli(A:type)(h1 h2:A)(t:<list A>)(x:A).
    ncong (cons A ** *)
          (cons A h1 (cons A h2 t))
          (cons A x (nil A))
          clash (cons ! h2 t)
                (nil !).

Define list_not_length_1_from_length : Forall(A:type)
                                             (l:<list A>)
                                             (u:{ (lt (list_length ! l) (S (S Z))) = ff })
                                             (x:A).
                                         { l != (cons ! x (nil !)) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt_ IHl return Forall(u:{ (lt (list_length ! l) (S (S Z))) = ff })
                                                     (x:A).
                                                 { l != (cons ! x (nil !)) } with
      nil A' =>
        foralli(u:{ (lt (list_length ! l) (S (S Z))) = ff }).
          contra trans symm u
                 trans hypjoin (lt (list_length ! l) (S (S Z)))
                               tt
                            by lp end
                       clash tt ff
            Forall(x:A).
              { l != (cons ! x (nil !)) }
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt_ in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt_ in
        [ induction(tt_:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = tt_ })
                                                               (u:{ (lt (list_length ! l) (S (S Z))) = ff })
                                                               (x:A).
                                                           { l != (cons ! x (nil !)) } with
            nil A'' =>
              foralli(ttpf:{ t = tt_ })
                     (u:{ (lt (list_length ! l) (S (S Z))) = ff }).
                contra trans symm u
                       trans hypjoin (lt (list_length ! l) (S (S Z)))
                                     tt
                                  by lp
                                     trans ttpf ttp end
                             clash tt ff
                  Forall(x:A).
                    { l != (cons ! x (nil !)) }
          | cons A'' h' t' =>
              abbrev h'cast = cast h' by symm inj <list *> ttt in
              abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in
              foralli(ttpf:{ t = tt_ })
                     (u:{ (lt (list_length ! l) (S (S Z))) = ff })
                     (x:A).
                trans lp
                trans cong (cons ! h *) trans ttpf ttp
                      [list_not_length_1 A hcast h'cast t'cast x]
          end tcast join t t ]
    end.

Define list1_elt : Forall(A:type)
                         (l:<list A>)
                         (u:{ l != (nil !) })
                         (v:{ (lt (list_length ! l) (S (S Z))) = tt }).
                   Exists(x:A).
                     { l = (cons ! x (nil !)) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt_ IHl return Forall(u:{ l != (nil !) })
                                                     (v:{ (lt (list_length ! l) (S (S Z))) = tt }).
                                               Exists(x:A).
                                                 { l = (cons ! x (nil !)) } with
      nil A' =>
        foralli(u:{ l != (nil !) })
               (v:{ (lt (list_length ! l) (S (S Z))) = tt }).
          contra trans symm lp
                       u
            Exists(x:A).
              { l = (cons ! x (nil !)) }
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt_ in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt_ in
        foralli(u:{ l != (nil !) })
               (v:{ (lt (list_length ! l) (S (S Z))) = tt }).
          [ induction(tt_:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = tt_ }).
                                                           Exists(x:A).
                                                             { l = (cons ! x (nil !)) } with
              nil A'' =>
                foralli(ttpf:{ t = tt_ }).
                  existsi hcast
                          { l = (cons ! * (nil !)) }
                    trans lp
                          cong (cons ! h *)
                               trans ttpf ttp
            | cons A'' h' t' =>
                abbrev t'cast = cast t' by cong <list *> symm inj <list *> ttt in
                foralli(ttpf:{ t = tt_ }).
                  contra trans symm v
                         trans cong (lt (list_length ! *) (S (S Z))) lp
                         trans cong (lt (list_length ! (cons ! h *)) (S (S Z))) trans ttpf ttp
                         trans join (lt (list_length ! (cons ! h (cons ! h' t'))) (S (S Z)))
                                    (lt (list_length ! t') Z)
                         trans [lt_Z terminates (list_length A t'cast) by list_length_total]
                               clash ff tt
                    Exists(x:A).
                      { l = (cons ! x (nil !)) }
            end tcast join t t ]
    end.

Define nonnil_list_has_head : Forall(A:type)
                                    (l:<list A>)
                                    (lne:{ l != (nil !) }).
                              Exists(h:A)
                                    (t:<list A>).
                                { l = (cons ! h t) } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) }).
                                              Exists(h:A)
                                                    (t:<list A>).
                                                { l = (cons ! h t) } with
      nil A' =>
        foralli(lne:{ l != (nil !) }).
          contra trans lp symm lne
            Exists(h:A)
                  (t:<list A>).
              { l = (cons ! h t) }
    | cons A' h t =>
        abbrev hcast = cast h by symm inj <list *> lt in
        abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
        foralli(lne:{ l != (nil !) }).
          existsi hcast
                  Exists(t:<list A>).
                    { l = (cons ! * t) }
            existsi tcast
                    { l = (cons ! h *) }
              lp
    end.

Define last_elt: Fun(A:type)(l:<list A>).A :=
  fun last_elt(A:type)(l:<list A>):A.
  match l by lp lt return A with
    nil A' =>
      abort A
  | cons A' h t =>
      match t by tp tt return A with
        nil A'' =>
          cast h by symm inj <list *> lt
      | cons A'' h' t' =>
          (last_elt A cast t by cong <list *> symm inj <list *> lt)
      end
  end.

Define last_elt_parttotal: Forall(A:type)(l:<list A>)(lne:{ l != (nil !) }).Exists(o:A).{ (last_elt ! l) = o } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) }).Exists(o:A).{ (last_elt ! l) = o } with
      nil A' =>
        foralli(lne:{ l != (nil !) }).
          contra trans lp
                       symm lne
            Exists(o:A).{ (last_elt ! l) = o }
    | cons A' h t =>
        foralli(lne:{ l != (nil !) }).
          abbrev hcast = cast h by symm inj <list *> lt in
          abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
          [ induction(tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = tt }).Exists(o:A).{ (last_elt ! l) = o } with
              nil A'' =>
                foralli(ttpf:{ t = tt }).
                  existsi hcast
                          { (last_elt ! l) = * }
                    hypjoin (last_elt ! l)
                            h
                         by lp
                            trans ttpf ttp end
            | cons A'' h' t' =>
                foralli(ttpf:{ t = tt }).
                  abbrev tne = trans ttpf
                               trans ttp
                                     clash (cons ! h' t') (nil !) in
                  existse [IHl tcast tne]
                    foralli(o:A)(opf:{ (last_elt ! t) = o }).
                      existsi o
                              { (last_elt ! l) = * }
                        hypjoin (last_elt ! l)
                                o
                             by lp
                                symm opf
                                trans ttpf ttp end
            end tcast
                join t t ]
    end.

Define skip_last_elt: Fun(A:type)(l:<list A>).<list A> :=
  fun skip_last_elt(A:type)(l:<list A>):<list A>.
  match l by lp lt return <list A> with
    nil A' =>
      abort <list A>
  | cons A' h t =>
      match t by tp tt return <list A> with
        nil A'' =>
          (nil A)
      | cons A'' h' t' =>
          (cons A cast h by symm inj <list *> lt (skip_last_elt A cast t by cong <list *> symm inj <list *> lt))
      end
  end.

Define skip_last_elt_parttotal: Forall(A:type)(l:<list A>)(lne:{ l != (nil !) }).Exists(o:<list A>).{ (skip_last_elt ! l) = o } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return Forall(lne:{ l != (nil !) }).Exists(o:<list A>).{ (skip_last_elt ! l) = o } with
      nil A' =>
        foralli(lne:{ l != (nil !) }).
          contra trans lp
                       symm lne
            Exists(o:<list A>).{ (skip_last_elt ! l) = o }
    | cons A' h t =>
        foralli(lne:{ l != (nil !) }).
          abbrev hcast = cast h by symm inj <list *> lt in
          abbrev tcast = cast t by cong <list *> symm inj <list *> lt in
          [ induction(tt:<list A>) by ttp ttt IHtt return Forall(ttpf:{ t = tt }).Exists(o:<list A>).{ (skip_last_elt ! l) = o } with
              nil A'' =>
                foralli(ttpf:{ t = tt }).
                  existsi (nil A)
                          { (skip_last_elt ! l) = * }
                    hypjoin (skip_last_elt ! l)
                            (nil !)
                         by lp
                            trans ttpf ttp end
            | cons A'' h' t' =>
                foralli(ttpf:{ t = tt }).
                  abbrev tne = trans ttpf
                               trans ttp
                                     clash (cons ! h' t') (nil !) in
                  existse [IHl tcast tne]
                    foralli(o:<list A>)(opf:{ (skip_last_elt ! t) = o }).
                      existsi (cons A hcast o)
                              { (skip_last_elt ! l) = * }
                        hypjoin (skip_last_elt ! l)
                                (cons ! h o)
                             by lp
                                symm opf
                                trans ttpf ttp end
            end tcast
                join t t ]
    end.

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

Define eqlist : Fun(A:type)(owned l1 l2:<list A>)
                   (eqA:Fun(owned x1 x2:A).bool).bool :=
  fun eqlist(A:type)(owned l1 l2:<list A>)(eqA:Fun(owned x1 x2:A).bool):bool.
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
          (and (eqA h1cast h2cast) (eqlist A t1cast t2cast eqA))
      end
  end.

Define eqlist_total : Forall(A:type)(l1 l2:<list A>)(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).Exists(o:bool).{ (eqlist ! l1 l2 eqA) = o } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).Exists(o:bool).{ (eqlist ! l1 l2 eqA) = o } with
      nil A1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).Exists(o:bool).{ (eqlist ! l1 l2 eqA) = o } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
              existsi tt
                      { (eqlist ! l1 l2 eqA) = * }
                hypjoin (eqlist ! l1 l2 eqA)
                        tt
                     by l1p
                        l2p end
        | cons A2 h2 t2 =>
            foralli(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
              existsi ff
                      { (eqlist ! l1 l2 eqA) = * }
                hypjoin (eqlist ! l1 l2 eqA)
                        ff
                     by l1p
                        l2p end
        end
    | cons A1 h1 t1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).Exists(o:bool).{ (eqlist ! l1 l2 eqA) = o } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
              existsi ff
                      { (eqlist ! l1 l2 eqA) = * }
                hypjoin (eqlist ! l1 l2 eqA)
                        ff
                     by l1p
                        l2p end
        | cons A2 h2 t2 =>
            foralli(eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o }).
              abbrev h1cast = cast h1 by symm inj <list *> l1t in
              abbrev t1cast = cast t1 by cong <list *> symm inj <list *> l1t in
              abbrev h2cast = cast h2 by symm inj <list *> l2t in
              abbrev t2cast = cast t2 by cong <list *> symm inj <list *> l2t in
              existse [IHl1 t1cast t2cast eqA eqA_total]
                foralli(o2:bool)(o2pf:{ (eqlist ! t1 t2 eqA) = o2 }).
                  existse [and_total terminates (eqA h1cast h2cast) by eqA_total o2]
                    foralli(o:bool)(opf:{ (and (eqA h1 h2) o2) = o }).
                      existsi o
                              { (eqlist ! l1 l2 eqA) = * }
                        trans hypjoin (eqlist ! l1 l2 eqA)
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
                        (u:{ (eqlist ! l1 l2 eqA) = tt }).
                    { l1 = l2 } :=
  foralli(A:type).
    induction(l1:<list A>) by l1p l1t IHl1 return Forall(l2:<list A>)
                                                        (eqA:Fun(x1 x2:A).bool)
                                                        (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                                                        (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                                                        (u:{ (eqlist ! l1 l2 eqA) = tt }).
                                                    { l1 = l2 } with
      nil A1 =>
        induction(l2:<list A>) by l2p l2t IHl2 return Forall(eqA:Fun(x1 x2:A).bool)
                                                            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                                                            (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                                                            (u:{ (eqlist ! l1 l2 eqA) = tt }).
                                                        { l1 = l2 } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist ! l1 l2 eqA) = tt }).
              hypjoin l1 l2 by l1p l2p end
        | cons A2 h2 t2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist ! l1 l2 eqA) = tt }).
              contra trans hypjoin ff
                                   (eqlist ! l1 l2 eqA)
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
                                                            (u:{ (eqlist ! l1 l2 eqA) = tt }).
                                                        { l1 = l2 } with
          nil A2 =>
            foralli(eqA:Fun(x1 x2:A).bool)
                   (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                   (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                   (u:{ (eqlist ! l1 l2 eqA) = tt }).
              contra trans hypjoin ff
                                   (eqlist ! l1 l2 eqA)
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
                   (u:{ (eqlist ! l1 l2 eqA) = tt }).
              existse [eqlist_total A t1cast t2cast eqA eqA_total]
                foralli(o2:bool)(o2pf:{ (eqlist ! t1 t2 eqA) = o2 }).
                  abbrev eqlist_is_and_eqA_o2 =
                                                      symm trans symm u
                                                                 hypjoin (eqlist ! l1 l2 eqA)
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
                                            hypjoin (eqlist ! l1 l2 eqA)
                                                    (and (eqA h1 h2) (eqlist ! t1 t2 eqA))
                                                 by l1p
                                                    l2p
                                                    taileq end in
                  abbrev eqAeq = [eqA_eq h1cast h2cast [andtt_e1 terminates (eqA h1cast h2cast) by eqA_total
                                                                 o2
                                                                 eqlist_is_and_eqA_o2]] in
                  trans l1p
                  trans cong (cons ! * t1) eqAeq
                  trans cong (cons ! h2 *) taileq
                        symm l2p
        end
    end.

Define member : Fun(A:type)
                   (x:A)
                   (l:<list A>)
                   (eqA:Fun(x1 x2:A).bool).bool :=
  fun member(A:type)
            (x:A)
            (l:<list A>)
            (eqA:Fun(x1 x2:A).bool):bool.
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
            foralli(zr:bool)(zrpf:{ (member ! x t eqA) = zr }).
              existse [or_total terminates (eqA x hcast) by eqA_total zr]
                foralli(z:bool)(zpf:{ (or (eqA x h) zr) = z }).
                  existsi z
                          { (member ! x l eqA) = * }
                    trans cong (member ! x * eqA) lp
                    trans join (member ! x (cons ! h t) eqA)
                               (or (eqA x h) (member ! x t eqA))
                    trans cong (or (eqA x h) *) zrpf
                          zpf
    end.

%-

Define test := (nth nat (S (S Z))
                   (cons nat (S Z)
                   (cons nat (S (S Z))
                   (cons nat (S (S (S Z))) (nil nat))))).

Set "print_parsed".

Interpret test.

-%
