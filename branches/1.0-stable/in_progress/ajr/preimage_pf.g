Include "preimage.g".
Include "subset_pf.g".
Include "range.g".
Include "domain.g".

Define preimage_pf :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( pi : <preimage A B f g> ) : <preimage_P A B f g (preimage_data A B f g pi)>.
  match pi with
    mk_preimage _ _ _ _ a u =>
      (eq_subset_def_P B g (f a) (f (preimage_data A B f g pi))
                       cong (f *) hypjoin a (preimage_data A B f g pi) by pi_eq end
                       u)    
  end.
  
  
  
