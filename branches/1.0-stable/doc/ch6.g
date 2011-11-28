%- the "trusted" option tells Guru not to check the proofs 
   Defined in the given file or any included by it. -%

Include trusted "../lib/list.g".

Inductive nlist : type :=
  nnil : nlist
| ncons : Fun(n:nat)(l:nlist).nlist.

Define nappend : Fun(l1 l2:nlist).nlist :=
  fun nappend(l1 l2:nlist):nlist.
    match l1 with
      nnil => l2
    | ncons n l1' => (ncons n (nappend l1' l2))
    end.
     
Define append' : Fun(A:type)(l1 l2:<list A>).<list A> :=
  fun append'(A:type)(l1 l2:<list A>):<list A>.
    match l1 with
      nil _ => l2
    | cons _ a l1' => (cons A a (append' A l1' l2))
    end.

Classify append'.

Define append'_assoc : 
  Forall(A:type)(l1 l2 l3 : <list A>). { (append' l1 (append' l2 l3)) = (append' (append' l1 l2) l3) } :=
foralli(A:type).
induction(l1:<list A>) return Forall(l2 l3 : <list A>). { (append' l1 (append' l2 l3)) = (append' (append' l1 l2) l3) } with
  nil _ => 
  foralli(l2 l3 : <list A>). 
  trans cong (append' * (append' l2 l3)) l1_eq
  trans join (append' nil (append' l2 l3)) (append' (append' nil l2) l3)
        cong (append' (append' * l2) l3) symm l1_eq
| cons _ a l1' =>
  foralli(l2 l3 : <list A>).
  trans cong (append' * (append' l2 l3)) l1_eq
  trans join (append' (cons a l1') (append' l2 l3)) (cons a (append' l1' (append' l2 l3)))
  trans cong (cons a *) [l1_IH l1' l2 l3]
  trans join (cons a (append' (append' l1' l2) l3)) (append' (append' (cons a l1') l2) l3)
        cong (append' (append' * l2) l3) symm l1_eq
end.

Define foldr' : Fun(A B:type)(f:Fun(a:A)(b:B).B)(b:B)(l:<list A>).B :=
  fun foldr'(A B:type)(f:Fun(a:A)(b:B).B)(b:B)(l:<list A>):B.
    match l with
      nil _ => b
    | cons _ a l' => (f a (foldr' A B f b l'))
    end.

Define length' := fun(A:type)(l:<list A>).(foldr' A nat fun(a:A)(n:nat).(S n) Z l).

Define map' := 
  fun(A B:type)(f:Fun(x:A).B)(l:<list A>).
    (foldr' A <list B> fun(x:A)(l2:<list B>).(cons B (f x) l2) (nil B) l).

Define spec concat : Fun(A:type)(l:<list <list A>>).<list A> :=
  fun(A:type)(l:<list <list A>>).
    (foldr <list A> <list A> Unit unit fun(u:Unit)(l1 l2:<list A>).(append A l1 l2) (nil A) l).