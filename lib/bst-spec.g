Include "minmax.g".

Inductive bst : Fun(l u : nat).type :=
  leaf : Fun(spec a:nat).<bst a a>
| node : Fun(a:nat)(spec l1 u1 l2 u2:nat)
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

Define bst_in : Fun(x:nat)(spec l u:nat)(t:<bst l u>). bool :=
  fun bst_in(x:nat)(spec l u:nat)(t:<bst l u>): bool.
    match t with
      leaf _ => ff
    | node a l1 u1 l2 u2 t1 t2 q1 q2 =>
      match (eqnat x a) with
        ff => 
          match (le x a) with
            ff => (bst_in x l2 u2 t2)
          | tt => (bst_in x l1 u1 t1)
          end
      | tt => tt
      end
    end.

Define bst_in_le1
 : Forall(x l u:nat)(t:<bst l u>)(u:{(bst_in x t) = tt}). { (le l x) = tt } :=
 foralli(x:nat).
 induction(l u:nat)(t:<bst l u>) return
   Forall(u:{(bst_in x t) = tt}). { (le l x) = tt } with
   leaf _ => 
     foralli(u:{(bst_in x t) = tt}).
     contra
       trans symm u
       trans cong (bst_in x *) t_eq
       trans join (bst_in x leaf) ff
             clash ff tt
     { (le l x) = tt }
 | node a l1 u1 l2 u2 t1 t2 q1 q2 => 
     foralli(u:{(bst_in x t) = tt}).
     case (eqnat x a) by v1 _ with
       ff =>
       case (le x a) by v2 _ with
         ff => [le_trans l1 a x 
                  [le_trans l1 u1 a [bst_bounds l1 u1 t1] q1]
                  [le_ff_implies_le x a v2]]
       | tt => [t_IH l1 u1 t1 
                  symm
                  trans symm u
                        hypjoin (bst_in x t) (bst_in x t1)
                        by v1 v2 t_eq end]
       end
     | tt => 
       trans cong (le l *) [eqnatEq x a v1]
             [le_trans l1 u1 a
                [bst_bounds l1 u1 t1]
                q1]
     end
  end.