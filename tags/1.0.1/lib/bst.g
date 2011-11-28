Include "minmax.g".

Inductive bst : Fun(l u : nat).type :=
  leaf : Fun(a:nat).<bst a a>
| node : Fun(a l1 u1 l2 u2:nat)
            (t1 : <bst l1 u1>)
            (t2 : <bst l2 u2>)
            (q1:{ (le u1 a) = tt})
            (q2:{ (le a l2) = tt}).
            <bst l1 u2>.

Define bst_bounds : Forall(l u:nat)(b:<bst l u>). { (le l u) = tt} :=
  induction(l u:nat)(b:<bst l u>) return { (le l u) = tt}
    with
    leaf _ => trans cong (le l *) inj <bst ** *> b_Eq
                    [le_refl l] 
  | node a _ u1 l2 _ t1 t2 q1 q2 => 
    [le_trans l a u
       [le_trans l u1 a [b_IH l u1 t1] q1]
       [le_trans a l2 u q2 [b_IH l2 u t2]]]
  end.

Define bst_insert 
  : Fun(l u : nat)
       (t:<bst l u>)
       (x:nat).
       <bst (min x l) (max x u)> :=
  fun bst_insert(l u : nat)
                (t:<bst l u>)
                (x:nat):
      <bst (min x l) (max x u)>.
    match t with
      leaf a =>
        match (le a x) by q1 _ with
          ff => abort <bst (min x l) (max x u)>                    % case 1
        | tt => abort <bst (min x l) (max x u)>                    % case 2
        end
    | node a _ u1 l2 _ t1 t2 q1 q2 => 
      match (le a x) by q3 _ with
        ff => abort <bst (min x l) (max x u)>                      % case 3
      | tt => abort <bst (min x l) (max x u)>                      % case 4
      end
    end.
             