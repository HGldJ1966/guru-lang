Include "plus.g".


Inductive list : Fun(A:type)(n:nat). type :=
  nil : Fun(A:type). <list A Z>
| cons : Fun(A:type)(n:nat)(a:A)(l:<list A n>).<list A (S n)>.

Define append : Fun(A:type)(n m:nat)(l1 : <list A n>)(l2 : <list A m>).
                 <list A (plus n m)> :=
fun append(A:type)(n m:nat)(l1 : <list A n>)(l2 : <list A m>):
                 <list A (plus n m)>.
    match l1 by u v return <list A (plus n m)> with
      nil B => cast l2 by
                cong <list A *>
                 symm trans
                        cong (plus * m)
                            inj <list ** *> v
                        join (plus Z m) m
    | cons A' n' x l1' => 
       cast
          (cons A' (plus n' m) x (append A' n' m l1'
                                    cast l2 by cong <list * m>
                                                 inj <list * **> v)) 
       by trans
            cong <list * (S (plus n' m))>
              symm inj <list * **> v
            cong <list A *>
               trans
                 symm join (plus (S n') m)
                           (S (plus n' m))
                 cong (plus * m)
                   symm inj <list ** *> v
    end.


Define head : Fun(A:type)(n:nat)(l:<list A (S n)>). A :=
  fun(A:type)(n:nat)(l:<list A (S n)>).
    match l by x1 x2 return A with
      nil A' => abort A
    | cons A' n' x' l' => cast x' by symm inj <list * **> x2
    end.

Define head_total : Forall(A:type)(n:nat)(l:<list A (S n)>).
                    Exists(x:A). { (head ! n l) = x } :=
  foralli(A:type)(n:nat).
    induction(l:<list A (S n)>) by x1 x2 IH 
    return Exists(x:A). { (head ! n l) = x } with
      nil A' => contra trans inj <list ** *> x2 
                             clash Z (S n)
                 Exists(x:A). { (head ! n l) = x }
    | cons A' n' x' l' => existsi cast x' by symm inj <list * **> x2
                          { (head ! n l) = * }
                          trans cong (head ! n *) x1
                                join (head ! n (cons ! n' x' l'))
                                     x'
    end.
    
Define sorted : Fun(s : nat)( l : <list nat s>).bool :=
	fun sorted(s : nat)( l : <list nat s>) : bool.
	match l by x1 x2 return bool with
	nil nat  => tt
	| cons A' n' x' l' => 
		match l' by y1 y2 return bool with
			nil A'' => tt
			| cons A'' n'' x'' l'' => (and (le cast x' by symm inj <list * **> x2 
				cast x'' by trans symm inj <list * **>  y2 symm inj <list * **> x2) (sorted n' 
				cast l' by cong <list * n'> symm inj <list * **> x2 )) 
		end
	end.
		    

Define append_assoc : Forall(A:type)(n1 : nat)(l1 : <list A n1>)
                      (n2 n3 : nat)(l2 : <list A n2>)(l3 : <list A n3>).
                      { (append ! (plus n1 n2) n3
                            (append ! n1 n2 l1 l2) l3) =
                        (append ! n1 (plus n2 n3)
                            l1 (append ! n2 n3 l2 l3)) } :=
  foralli(A:type).
  induction(n1:nat)(l1:<list A n1>) by x1 x2 IH return Forall(n2 n3 : nat)
                      (l2 : <list A n2>)(l3 : <list A n3>).
                      { (append ! (plus n1 n2) n3
                            (append ! n1 n2 l1 l2) l3) =
                        (append ! n1 (plus n2 n3)
                            l1 (append ! n2 n3 l2 l3)) } with
    nil A' => foralli(n2 n3 : nat)
               (l2 : <list A n2>)(l3 : <list A n3>). 
           % transform the LHS to (append ! n2 n3 l2 l3)
           trans cong (append ! (plus n1 n2) n3
                          (append ! n1 n2 * l2) l3) 
                   x1
           trans cong (append ! (plus * n2) n3
                          (append ! * n2 (nil !) l2) l3)
                   inj <list ** *> x2
           trans join (append ! (plus Z n2) n3
                          (append ! Z n2 (nil !) l2) l3)
                      (append ! n1 (plus n2 n3)
                            (nil !) (append ! n2 n3 l2 l3))
           symm cong (append ! n1 (plus n2 n3)
                            * (append ! n2 n3 l2 l3)) x1
   | cons A' n1' x' l1' => 
      foralli(n2 n3 : nat)(l2 : <list A n2>)(l3 : <list A n3>). 
            trans cong (append ! (plus n1 n2) n3
                         (append ! n1 n2 * l2) l3) x1
            trans cong (append ! (plus n1 n2) n3 * l3)
                    join (append ! n1 n2 (cons ! n1' x' l1') l2)
                         (cons ! (plus n1' n2) x' (append ! n1' n2 l1' l2))
            trans join (append ! (plus n1 n2) n3 
                          (cons ! (plus n1' n2) x'
                             (append ! n1' n2 l1' l2)) l3)
                       (cons ! (plus (plus n1' n2) n3) x'
                          (append ! (plus n1' n2) n3
                              (append ! n1' n2 l1' l2) l3))
            trans cong (cons ! (plus (plus n1' n2) n3) x' *)
                          [IH n1' cast l1' by cong <list * n1'> 
                                                inj <list * **> symm x2
                              n2 n3 l2 l3]
            symm
            trans cong (append ! n1 (plus n2 n3)
                            * (append ! n2 n3 l2 l3)) x1
            trans join (append ! n1 (plus n2 n3)
                            (cons ! n1' x' l1') (append ! n2 n3 l2 l3))
                       (cons ! (plus n1' (plus n2 n3)) x' 
                         (append ! n1' (plus n2 n3) l1' 
                            (append ! n2 n3 l2 l3)))
                  cong (cons ! * x' 
                         (append ! n1' (plus n2 n3) l1' 
                            (append ! n2 n3 l2 l3)))
                    symm [plus_assoc n1' n2 n3]
 end.

Define map : Fun(A B:type)(n:nat)(f:Fun(x:A).B)(l:<list A n>). <list B n> :=
  fun map(A B:type)(n:nat)(f:Fun(x:A).B)(l:<list A n>): <list B n>.
    match l by x1 x2 return <list B n> with
      nil A' => cast (nil B) by cong <list B *> symm inj <list ** *> x2
    | cons A' n' x' l' =>
        cast (cons B n' (f cast x' by symm inj <list * **> x2)
                (map A B n' f cast l' by cong <list * n'> 
                                          symm inj <list * **> x2))
        by cong <list B *> symm inj <list ** *> x2
    end.

Define four := (S (S (S (S Z)))).

Define foo : <list nat (S (S Z))> := (map nat nat (S (S Z))
                                       (plus (S (S (S Z))))
                                       (cons nat (S Z) four
                                          (cons nat Z four (nil nat)))).
%-
Define map_append : Forall(A B:type)(n1 n2:nat)(f:Fun(x:A).B)
                          (l1:<list A n1>)(l2:<list A n2>).
                    { (map ! ! (plus n1 n2) f (append ! n1 n2 l1 l2)) =
                      (append ! n1 n2 (map ! ! n1 f l1) (map ! ! n2 f l2)) } :=
  foralli(A B:type)(n1 n2:nat)(f:Fun(x:A).B)
         (l1:<list A n1>)(l2:<list A n2>).
   [ foralli(n2:nat)(f:Fun(x:A).B)(l2:<list A n2>).
      induction(n1:nat)(l1:<list A n1>) by x1 x2 IH 
      return { (map ! ! (plus n1 n2) f (append ! n1 n2 l1 l2)) =
               (append ! n1 n2 (map ! ! n1 f l1) (map ! ! n2 f l2)) } with
        nil A' => trans cong (map ! ! (plus n1 n2) f (append ! n1 n2 * l2)) x1
                  trans join (map ! ! (plus n1 n2) f 
                                (append ! n1 n2 (nil !) l2))
                             (append ! n1 n2 (map ! ! n1 f (nil !))
                                             (map ! ! n2 f l2))
                        cong (append ! n1 n2 (map ! ! n1 f *)
                                             (map ! ! n2 f l2)) symm x1
      | cons A' n1' x' l1' => 
          trans cong (map ! ! (plus n1 n2) f (append ! n1 n2 * l2)) x1
          trans join (map ! ! (plus n1 n2) f 
                        (append ! n1 n2 (cons ! n1' x' l1') l2))
                     (cons ! (plus n1' n2) (f x') 
                        (map ! ! (plus n1' n2) f (append ! n1' n2 l1' l2)))
          trans cong (cons ! (plus n1' n2) (f x') *) 
                  [IH n1' cast l1' by cong <list * n1'> 
                                        inj <list * **> symm x2]
          trans join (cons ! (plus n1' n2) (f x') 
                        (append ! n1' n2 (map ! ! n1' f l1') 
                                         (map ! ! n2 f l2)))
                     (append ! n1' n2 (map ! ! n1' f (cons ! n1' x' l1')) 
                                      (map ! ! n2 f l2))
          cong (append ! n1' n2 (map ! ! n1' f *) (map ! ! n2 f l2)) 
                  symm x1
               %- cong (append ! * n2 (map ! ! * f l1) (map ! ! n2 f l2))
                  symm inj <list ** *> x2 -%

      end
     n2 f l2 n1 l1].
-%
