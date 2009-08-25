Include trusted "../guru-lang/lib/list.g".

%-

Define member_fill 
  : Forall(A:type)(x:A)(eqA:Fun(x y:A).bool)
          (eqA_tot:Forall(x y:A).Exists(b:bool). { (eqA x y) = b})
          (l:<list A>)
          (u:{(member x l eqA) = tt}). 
     Exists(l1 l2:<list A>)(h:A). { (eqA x h) } :=
  foralli(A:type)(x:A)(eqA:Fun(x y:A).bool).
    induction(l:<list A>) 
    return Forall(u:{(member x l eqA) = tt}). 
             Exists(l1 l2:<list A>)(h:A). { (eqA x h) }
    with
      nil _ => 
      foralli(u:{(member x l eqA) = tt}).
        contra trans symm u 
               trans cong (member x * eqA) l_eq
               trans join (member x nil eqA) ff
                     clash ff tt
        Exists(l1 l2:<list A>)(h:A). { (eqA x h) }
    | cons _ h t => 
      foralli(u:{(member x l eqA) = tt}).
        existse [eqA_tot x h]
        foralli(b:bool)(b_eq:{(eqA x h) = b}).
          case b with
            ff => trans symm u
                  trans cong (member x * eqA) l_eq
-%                  

Define fill_plus : Forall(A:type)(a:A)(n m:nat). { (fill a (plus n m)) = (append (fill a n) (fill a m)) } :=
  foralli(A:type)(a:A).
  induction(n:nat) return Forall(m:nat).{ (fill a (plus n m)) = (append (fill a n) (fill a m)) } 
  with
    Z => 
    foralli(m:nat).
      trans cong (fill a (plus * m)) n_eq
      trans join (fill a (plus Z m)) (append (fill a Z) (fill a m))
            cong (append (fill a *) (fill a m)) symm n_eq
  | S n' => 
    foralli(m:nat).
      trans cong (fill a (plus * m)) n_eq
      trans join (fill a (plus (S n') m)) (cons a (fill a (plus n' m)))
      trans cong (cons a *) [n_IH n' m]
      trans join (cons a (append (fill a n') (fill a m))) (append (fill a (S n')) (fill a m))
            cong (append (fill a *) (fill a m)) symm n_eq
  end.

Define map_compose:
  Forall(A B C:type)
        (f:Fun(u:Unit)(x:A).B)
        (g:Fun(u:Unit)(x:B).C)
        (l:<list A>).
    { (map unit g (map unit f l)) = (map unit fun(u x).(g u (f u x)) l) } :=
  foralli(A B C:type)
         (f:Fun(u:Unit)(x:A).B)
         (g:Fun(u:Unit)(x:B).C).
  induction(l:<list A>) return { (map unit g (map unit f l)) = (map unit fun(u x).(g u (f u x)) l) }
  with
    nil _ => trans cong (map unit g (map unit f *)) l_eq
             trans join (map unit g (map unit f nil)) (map unit fun(u x).(g u (f u x)) nil)
                   cong (map unit fun(u x).(g u (f u x)) *) symm l_eq
  | cons _ a l' => 
    trans cong (map unit g (map unit f *)) l_eq
    trans join (map unit g (map unit f (cons a l'))) (cons (g unit (f unit a)) (map unit g (map unit f l')))
    trans cong (cons (g unit (f unit a)) *) [l_IH l']
    trans join (cons (g unit (f unit a)) (map unit fun(u x).(g u (f u x)) l')) (map unit fun(u x).(g u (f u x)) (cons a l'))
          cong (map unit fun(u x).(g u (f u x)) *) symm l_eq
  end.
   

Define some : Fun(A C:type)(owned c:C)
                (f:Fun(owned c:C)(owned a:A).bool)(owned l:<list A>).bool :=
  fun(A C:type)(owned c:C)(f:Fun(owned c:C)(owned a:A).bool).
    (foldr A bool C c fun(owned c:C)(owned a:A)(b:bool).(or (f c a) b) ff).