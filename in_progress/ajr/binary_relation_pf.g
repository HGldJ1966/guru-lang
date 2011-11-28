Include "binary_relation.g".
Include "equality.g".


%===== if f is reflexive and f = g, then g is reflexive
%-
Define br_refl_P_pf : Forall( A : type )( f : Fun( a1 a2 : A ).bool )( brr : <br_refl_P A f> )
                            ( a : A ).{ (f a a) = tt } :=
foralli( A : type )( f : Fun( a1 a2 : A ).bool )( brr : <br_refl_P A f> )( a : A ).
  case brr with     
    br_refl_p _ _ u => trans refl (f a a)
                             [u a]
  end.
  -%
  
  
  
%-
Define br_refl_pf :=
fun( A : type )( br : <br_refl A> ) : <br_refl_P A (br_refl_data A br)>.
  match br with
    mk_br_refl _ _ u =>
      
  end.
-%