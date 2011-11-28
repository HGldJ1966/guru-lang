Include "eq_map.g".

Define eq_map_data_pf : Forall( A : type )( e : <eq_map A> )( a1 a2 : A )( ute : { (eq_map_data A e a1 a2) = tt } ). { a1 = a2 } :=
foralli( A : type )( e : <eq_map A> )( a1 a2 : A )( ute : { (eq_map_data e a1 a2) = tt } ).
  case e with
    mk_eq _ f u _ => [u a1 a2 
                        trans symm hypjoin (eq_map_data A e a1 a2) (f a1 a2) by e_eq end
                              ute]
  end.
  

Define eq_map_data_refl : Forall( A : type )( e : <eq_map A> )( a : A ). { (eq_map_data A e a a) = tt } :=
foralli( A : type )( e : <eq_map A> )( a : A ).
  case e with
    mk_eq _ f _ u_rfl => trans hypjoin (eq_map_data A e a a) (f a a) by e_eq end
                               [u_rfl a]
  end.
  
  
Define eq_map_data_symm : Forall( A : type )( e : <eq_map A> )( a1 a2 : A )
                            ( u : { (eq_map_data A e a1 a2) = tt } ).{ (eq_map_data A e a2 a1) = tt } :=
foralli( A : type )( e : <eq_map A> )( a1 a2 : A )( u : { (eq_map_data A e a1 a2) = tt } ).
  trans cong (eq_map_data A e * a1) symm [eq_map_data_pf A e a1 a2 u]
        [eq_map_data_refl A e a1].
        
  
Define eq_map_data_trans : Forall( A : type )( e : <eq_map A> )( a1 a2 a3 : A )
                             ( u12 : { (eq_map_data A e a1 a2) = tt } )
                             ( u23 : { (eq_map_data A e a2 a3) = tt } ). { (eq_map_data A e a1 a3) = tt } :=
foralli( A : type )( e : <eq_map A> )( a1 a2 a3 : A )
       ( u12 : { (eq_map_data A e a1 a2) = tt } )
       ( u23 : { (eq_map_data A e a2 a3) = tt } ). 
  trans cong (eq_map_data A e * a3) trans [eq_map_data_pf A e a1 a2 u12]
                                      [eq_map_data_pf A e a2 a3 u23]
        [eq_map_data_refl A e a3].


Define pf_eq_map_data : Forall( A : type )( e : <eq_map A> )( a1 a2 : A )( u : { a1 = a2 } ). { (eq_map_data A e a1 a2) = tt } :=
foralli( A : type )( e : <eq_map A> )( a1 a2 : A )( u : { a1 = a2 } ).
  trans cong (eq_map_data A e * a2) u
        [eq_map_data_refl A e a2].