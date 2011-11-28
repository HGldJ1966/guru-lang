Include "subset.g".
Include "range.g".
Include "domain.g".

%======= the statement a is in the preimage of the subset B|g under f   
%-
<preimage_P A B f g a>
  <fiber B B g (f a)>
    <range_P B B g (f a)>
    <subset_def_P B g (f a)>        %(f a) is in the subset of B defined by g, i.e. a is in the preimage of G|b
-%
Define type_family_abbrev preimage_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( a : A ). <fiber B B g (f a)>.


Define preimage_p :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( a : A )( b : B )
   ( u : { (g b) = (f a) } ) : <preimage_P A B f g a>.
   (subset_def_p B g (f a) b u).


Define preimage_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( a : A )
                             ( p : <preimage_P A B f g a> ). Exists( b : B ). { (g b) = (f a) } :=
foralli( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( a : A )
       ( p : <preimage_P A B f g a> ).
  case p with
    mk_fiber _ _ _ _ b u => 
      existsi cast b by symm inj <preimage_P ** * ** ** **> p_Eq { (g *) = (f a) }
        u
  end.


%======= the preimage of the subset B|g under f 
Inductive preimage : Fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B ). type :=
  mk_preimage : Fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( a : A )
                   ( u : <preimage_P A B f g a> ). <preimage A B f g>.


Define preimage_data :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).B )( pi : <preimage A B f g> ) : A.
  match pi with
    mk_preimage _ _ _ _ a _ => cast a by symm inj <preimage * ** ** **> pi_Eq
  end.



