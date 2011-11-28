Include "../lib/plus.g".

Inductive llist : Fun(A:type)(n:nat). type :=
  lnil : Fun(A:type). <llist A Z>
| lcons : Fun(A:type)(n:nat)(a:A)(l:<llist A n>).<llist A (S n)>.

Define append : Fun(A:type)(n m:nat)(l1 : <llist A n>)(l2 : <llist A m>).
                 <llist A (plus n m)> :=
fun append(A:type)(n m:nat)(l1 : <llist A n>)(l2 : <llist A m>):
                 <llist A (plus n m)>.
    match l1 by u v return <llist A (plus n m)> with
      lnil B => cast l2 by
                 cong <llist A *>
                   symm trans cong (plus * m) inj <llist ** *> v 
                              join (plus Z m) m
%                   hypjoin m (plus n m) by inj <llist ** *> v end
    | lcons A' n' x l1' => 
       cast
          (lcons A' (plus n' m) x (append A' n' m l1'
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

%Set "print_parsed".

Define head : Fun(A:type)(n:nat)(l:<llist A (S n)>). A :=
  fun(A:type)(n:nat)(l:<llist A (S n)>).
    match l by x1 x2 return A with
      lnil A' => abort A
    | lcons A' n' x' l' => cast x' by symm inj <llist * **> x2
    end.

Define head_total : Forall(A:type)(n:nat)(l:<llist A (S n)>).
                    Exists(x:A). { (head ! n l) = x } :=
  foralli(A:type)(n:nat).
    induction(l:<llist A (S n)>) by x1 x2 IH 
    return Exists(x:A). { (head ! n l) = x } with
      lnil A' => contra trans inj <llist ** *> x2 
                             clash Z (S n)
                 Exists(x:A). { (head ! n l) = x }
    | lcons A' n' x' l' => existsi cast x' by symm inj <llist * **> x2
                          { (head ! n l) = * }
                          trans cong (head ! n *) x1
                                join (head ! n (lcons ! n' x' l'))
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
    lnil A' => foralli(n2 n3 : nat)
               (l2 : <llist A n2>)(l3 : <llist A n3>). 
          hypjoin (append ! (plus n1 n2) n3
                          (append ! n1 n2 l1 l2) l3)
                  (append ! n1 (plus n2 n3)
                           l1 (append ! n2 n3 l2 l3))
             by x1 inj <llist ** *> x2 end
   | lcons A' n1' x' l1' => 
      foralli(n2 n3 : nat)(l2 : <llist A n2>)(l3 : <llist A n3>). 
            trans hypjoin (append ! (plus n1 n2) n3
                            (append ! n1 n2 l1 l2) l3)
                          (lcons ! (plus (plus n1' n2) n3) x'
                            (append ! (plus n1' n2) n3
                                (append ! n1' n2 l1' l2) l3))
                   by x1 end
            trans cong (lcons ! (plus (plus n1' n2) n3) x' *)
                          [IH n1' cast l1' by cong <llist * n1'> 
                                                inj <llist * **> symm x2
                              n2 n3 l2 l3]
            symm
            trans hypjoin (append ! n1 (plus n2 n3)
                            l1 (append ! n2 n3 l2 l3))
                          (lcons ! (plus n1' (plus n2 n3)) x' 
                            (append ! n1' (plus n2 n3) l1' 
                             (append ! n2 n3 l2 l3)))
                    by x1 end
                  cong (lcons ! * x' 
                         (append ! n1' (plus n2 n3) l1' 
                            (append ! n2 n3 l2 l3)))
                    symm [plus_assoc n1' n2 n3]
 end.

