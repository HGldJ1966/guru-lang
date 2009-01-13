Include "plus.g".
Include "bool.g".

Inductive llist : Fun(A:type)(n:nat).type :=
  llistn : Fun(A:type).<llist A Z>
| llistc : Fun(A:type)(a:A)(n:nat)(l:<llist A n>).
              <llist A (S n)>.

%Set "print_parsed".

Define append :=
fun append(A:type)(n m:nat)(l1 : <llist A n>)(l2 : <llist A m>):
          <llist A (plus n m)>.
    match l1 by u v return <llist A (plus n m)> with
      llistn B => cast l2 by
                cong <llist A *>
                 symm trans
                        cong (plus * m)
                            inj <llist ** *> v
                        join (plus Z m) m
    | llistc A' x n' l1' => 
       cast
          (llistc A' x (plus n' m) (append A' n' m l1'
                                    cast l2 by cong <llist * m>
                                                 inj <llist * **> v)) 
       by trans
            cong <llist * (S (plus n' m))>
              symm inj <llist * **> v
            cong <llist A *>
               trans
                 symm join (plus (S n') m)
                           (S (plus n' m))
                 cong (plus * m)
                   symm inj <llist ** *> v
    end.

Define head : Fun(A:type)(n:nat)(l:<llist A (S n)>). A :=
  fun(A:type)(n:nat)(l:<llist A (S n)>).
    match l by x1 x2 return A with
      llistn A' => abort A
    | llistc A' x' n' l' => cast x' by symm inj <llist * **> x2
    end.

Define head_total : Forall(A:type)(n:nat)(l:<llist A (S n)>).
                    Exists(x:A). { (head ! n l) = x } :=
  foralli(A:type)(n:nat).
    induction(l:<llist A (S n)>) by x1 x2 IH 
    return Exists(x:A). { (head ! n l) = x } with
      llistn A' => contra trans inj <llist ** *> x2 
                             clash Z (S n)
                 Exists(x:A). { (head ! n l) = x }
    | llistc A' x' n' l' => existsi cast x' by symm inj <llist * **> x2
                          { (head ! n l) = * }
                          trans cong (head ! n *) x1
                                join (head ! n (llistc ! x' n' l'))
                                     x'
    end.

Define append_assoc : Forall(A:type)(n1 : nat)(l1 : <llist A n1>)
                      (n2 n3 : nat)(l2 : <llist A n2>)(l3 : <llist A n3>).
                      { (append ! (plus n1 n2) n3
                            (append ! n1 n2 l1 l2) l3) =
                        (append ! n1 (plus n2 n3)
                            l1 (append ! n2 n3 l2 l3)) } :=
  foralli(A:type).
  induction(n1:nat)(l1:<llist A n1>) by x1 x2 IH return Forall(n2 n3 : nat)
                      (l2 : <llist A n2>)(l3 : <llist A n3>).
                      { (append ! (plus n1 n2) n3
                            (append ! n1 n2 l1 l2) l3) =
                        (append ! n1 (plus n2 n3)
                            l1 (append ! n2 n3 l2 l3)) } with
    llistn A' => foralli(n2 n3 : nat)
               (l2 : <llist A n2>)(l3 : <llist A n3>). 
           % transform the LHS to (append ! n2 n3 l2 l3)
           trans cong (append ! (plus n1 n2) n3
                          (append ! n1 n2 * l2) l3) 
                   x1
           trans cong (append ! (plus * n2) n3
                          (append ! * n2 (llistn !) l2) l3)
                   inj <llist ** *> x2
           trans join (append ! (plus Z n2) n3
                          (append ! Z n2 (llistn !) l2) l3)
                      (append ! n1 (plus n2 n3)
                            (llistn !) (append ! n2 n3 l2 l3))
           symm cong (append ! n1 (plus n2 n3)
                            * (append ! n2 n3 l2 l3)) x1
   | llistc A' x' n1' l1' => 
      foralli(n2 n3 : nat)(l2 : <llist A n2>)(l3 : <llist A n3>). 
            trans cong (append ! (plus n1 n2) n3
                         (append ! n1 n2 * l2) l3) x1
            trans cong (append ! (plus n1 n2) n3 * l3)
                    join (append ! n1 n2 (llistc ! x' n1' l1') l2)
                         (llistc ! x' (plus n1' n2) (append ! n1' n2 l1' l2))
            trans join (append ! (plus n1 n2) n3 
                          (llistc ! x' (plus n1' n2)
                             (append ! n1' n2 l1' l2)) l3)
                       (llistc ! x' (plus (plus n1' n2) n3)
                          (append ! (plus n1' n2) n3
                              (append ! n1' n2 l1' l2) l3))
            trans cong (llistc ! x' (plus (plus n1' n2) n3) *)
                          [IH n1' cast l1' by cong <llist * n1'> 
                                                inj <llist * **> symm x2
                              n2 n3 l2 l3]
            symm
            trans cong (append ! n1 (plus n2 n3)
                            * (append ! n2 n3 l2 l3)) x1
            trans join (append ! n1 (plus n2 n3)
                            (llistc ! x' n1' l1') (append ! n2 n3 l2 l3))
                       (llistc ! x' (plus n1' (plus n2 n3)) 
                         (append ! n1' (plus n2 n3) l1' 
                            (append ! n2 n3 l2 l3)))
                  cong (llistc ! x' * 
                         (append ! n1' (plus n2 n3) l1' 
                            (append ! n2 n3 l2 l3)))
                    symm [plus_assoc n1' n2 n3]
 end.

Define map : Fun(A B:type)(n:nat)(f:Fun(x:A).B)(l:<llist A n>). <llist B n> :=
  fun map(A B:type)(n:nat)(f:Fun(x:A).B)(l:<llist A n>): <llist B n>.
    match l by x1 x2 return <llist B n> with
      llistn A' => cast (llistn B) by cong <llist B *> symm inj <llist ** *> x2
    | llistc A' x' n' l' =>
        cast (llistc B (f cast x' by symm inj <llist * **> x2) n' 
                (map A B n' f cast l' by cong <llist * n'> 
                                          symm inj <llist * **> x2))
        by cong <llist B *> symm inj <llist ** *> x2
    end.

Define four := (S (S (S (S Z)))).

Define foo : <llist nat (S (S Z))> := (map nat nat (S (S Z))
                                       (plus (S (S (S Z))))
                                       (llistc nat four (S Z) 
                                          (llistc nat four Z (llistn nat)))).
%-
Define map_append : Forall(A B:type)(n1 n2:nat)(f:Fun(x:A).B)
                          (l1:<llist A n1>)(l2:<llist A n2>).
                    { (map ! ! (plus n1 n2) f (append ! n1 n2 l1 l2)) =
                      (append ! n1 n2 (map ! ! n1 f l1) (map ! ! n2 f l2)) } :=
  foralli(A B:type)(n1 n2:nat)(f:Fun(x:A).B)
         (l1:<llist A n1>)(l2:<llist A n2>).
   [ foralli(n2:nat)(f:Fun(x:A).B)(l2:<llist A n2>).
      induction(n1:nat)(l1:<llist A n1>) by x1 x2 IH 
      return { (map ! ! (plus n1 n2) f (append ! n1 n2 l1 l2)) =
               (append ! n1 n2 (map ! ! n1 f l1) (map ! ! n2 f l2)) } with
        llistn A' => trans cong (map ! ! (plus n1 n2) f (append ! n1 n2 * l2)) x1
                  trans join (map ! ! (plus n1 n2) f 
                                (append ! n1 n2 (llistn !) l2))
                             (append ! n1 n2 (map ! ! n1 f (llistn !))
                                             (map ! ! n2 f l2))
                        cong (append ! n1 n2 (map ! ! n1 f *)
                                             (map ! ! n2 f l2)) symm x1
      | llistc A' x' n1' l1' => 
          trans cong (map ! ! (plus n1 n2) f (append ! n1 n2 * l2)) x1
          trans join (map ! ! (plus n1 n2) f 
                        (append ! n1 n2 (llistc ! x' n1' l1') l2))
                     (llistc ! (f x') (plus n1' n2)
                        (map ! ! (plus n1' n2) f (append ! n1' n2 l1' l2)))
          trans cong (llistc ! (f x') (plus n1' n2) *) 
                  [IH n1' cast l1' by cong <llist * n1'> 
                                        inj <llist * **> symm x2]
          trans join (llistc ! (f x') (plus n1' n2)
                        (append ! n1' n2 (map ! ! n1' f l1') 
                                         (map ! ! n2 f l2)))
                     (append ! n1' n2 (map ! ! n1' f (llistc ! x' n1' l1')) 
                                      (map ! ! n2 f l2))
          cong (append ! n1' n2 (map ! ! n1' f *) (map ! ! n2 f l2)) 
                  symm x1
               %- cong (append ! * n2 (map ! ! * f l1) (map ! ! n2 f l2))
                  symm inj <llist ** *> x2 -%

      end
     n2 f l2 n1 l1].
-%
