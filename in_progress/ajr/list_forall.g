Include "../../guru-lang/lib/list.g".

Define all_total : 
Forall(A C:type)(c:C)
      (l:<list A>)
      (f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o }).
      Exists(o:bool).{ (all A C c f l) = o } :=
foralli(A C:type)(c:C).
  induction (l:<list A>) by ul uL IHl return Forall(f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o }).
                                              Exists(o:bool).{ (all A C c f l) = o } with
    nil _ => foralli(f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o }).
               existsi tt { (all A C c f l) = * } hypjoin (all A C c f l) tt by ul end
  | cons _ a' l' => foralli(f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o }).
                      existse [[IHl l'] f f_total]
                              foralli( x : bool )( u : { (all A C c f l') = x } ).
                                existsi terminates (and terminates (f c a') by f_total  
                                                        terminates (all A C c f l') by [[IHl l'] f f_total] ) by and_tot
                                        { (all A C c f l) = * }
                                        hypjoin (all A C c f l) (and (f c a') (all A C c f l')) by ul end
  end.



Define allEq :
Forall(A C:type)(c:C)
      (f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o })
      (eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
      (eqAEq:Forall(x1 x2:A)(u:{(eqA x1 x2) = tt}). { x1 = x2 })
      (l:<list A>)( u : { (all A C c f l) = tt } ). 
      Forall( a : A )( ua : { (member A a l eqA) = tt } ). { (f c a) = tt } :=
foralli(A C:type)(c:C)
       (f:Fun(c:C)(a:A).bool)(f_total:Forall(c:C)(a:A).Exists(o:bool).{ (f a c) = o })
       (eqA:Fun(x1 x2:A).bool)(eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
       (eqAEq:Forall(x1 x2:A)(u:{(eqA x1 x2) = tt}). { x1 = x2 }).
  induction (l:<list A>) by ul uL IHl return Forall( u : { (all A C c f l) = tt } )
                                                         ( a : A )( ua : { (member A a l eqA) = tt } ). { (f c a) = tt } with
    nil _ => 
      foralli( u : { (all A C c f l) = tt } )( a : A )( ua : { (member A a l eqA) = tt } ).
        contra
          trans symm ua
          trans hypjoin (member A a l eqA) ff by ul end
                clash ff tt
          { (f c a) = tt } 
  | cons _ a' l' => 
      foralli( u : { (all A C c f l) = tt } )( a : A )( ua : { (member A a l eqA) = tt } ).
        case terminates (eqA a a') by eqA_total by uea ueA with
          ff => [ [IHl l']
                  [andtt_e2 terminates (f c a') by f_total 
                            terminates (all A C c f l') by [all_total A C c l' f f_total]
                            trans symm hypjoin (all A C c f l) (and (f c a') (all A C c f l')) by ul uea end
                                  u]
                  a
                  trans symm [or_def2ff (member A a l' eqA)]
                  trans [or_comm (member A a l' eqA) ff]
                  trans symm cong (or * (member A a l' eqA)) uea
                        trans symm hypjoin (member A a l eqA) (or (eqA a a') (member A a l' eqA)) by ul end
                              ua ]
        | tt => trans cong (f c *) [eqAEq a a' uea]
                      [andtt_e1 terminates (f c a') by f_total 
                                terminates (all A C c f l') by [all_total A C c l' f f_total]
                                trans symm hypjoin (all A C c f l) (and (f c a') (all A C c f l')) by ul uea end
                                      u]
        end
  end.

