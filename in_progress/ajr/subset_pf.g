Include "subset.g".
Include "equality.g".
Include "range_pf.g".

Define eq_subset_def_P :=
fun( A : type )( f : Fun( a : A ). A )( a1 a2 : A )( u : { a1 = a2 } )( s : <subset_def_P A f a1> ) : <subset_def_P A f a2>.
  (eq_range_P A A f a1 a2 u s).
  

Define subset_def_pf :=
fun( A : type )( f : Fun( a : A ). A )( s : <subset_def A f> ) : <fiber A A f (subset_def_data A f s)>.
  (eq_range_P A A f (range_data A A f s) (subset_def_data A f s)
              join (range_data A A f s) (subset_def_data A f s) (range_pf A A f s)).
  
  
Define subset_pf :=
fun( A : type )( s : <subset A> ) : <subset_def_P A (subset_f A s) (subset_data A s)>.
  match s with
    mk_subset _ f a r => (feq_range_P A A f (subset_f A s)
                                       (feq_p A A f (subset_f A s) foralli( a' : A ). hypjoin (f a') ((subset_f A s) a') by s_eq end)
                                       (subset_data A s)
                                       (eq_range_P A A f a (subset_data A s) hypjoin a (subset_data A s) by s_eq end r))
  end.


Define subset_subset_def :=
fun( A : type )( s : <subset A> ) : <subset_def A (subset_f A s)>.
  (mk_range A A (subset_f A s) (subset_data A s) (subset_pf A s)).
  
%-
Define powerset_data :=
fun( A : type )( p : <powerset A> ) : <subset_def A A (powerset_f A p)>.
  match p with
    mk_powerset _ f => 
%-
      abbrev ppd = (feq_P A A f (powerset_f A p)
                          foralli( a : A ).
                            hypjoin (f a) (powerset_f A p a) by p_eq end) in
-%
      (mk_range A A (powerset_f A p))
  end.
-%
  
