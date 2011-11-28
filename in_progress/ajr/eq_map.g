Include "../../guru-lang/lib/bool.g".
Include "binary_relation.g".



%=========== statement that f is an equality map for A
Inductive eq_map_P : Fun( A : type )( f : Fun( a1 a2 : A ). bool ).type :=
  mk_eq : Fun( A : type )( f : Fun( a1 a2 : A ). bool )
             ( u : Forall( a1 a2 : A )( uf : { (f a1 a2) = tt } ). { a1 = a2 } )
             ( u_rfl : <br_refl_P A f> ). <eq_map A>.
%- or this?
%note that reflexivity of f is implied in this scenario
Inductive eq_map : Fun( A : type ).type :=
  mk_eq : Fun( A : type )( f : Fun( a1 a2 : A ). bool )
             ( u : Forall( a1 a2 : A )( uf : { (f a1 a2) = tt } ). { a1 = a2 } )
             ( un : Forall( a1 a2 : A )( uf : { (f a1 a2) = tt } ). { a1 != a2 } ). <eq_map A>.
-%



%=========== an equality map for A
Inductive eq_map : Fun( A : type ).type :=
  mk_eq : Fun( A : type )( f : Fun( a1 a2 : A ). bool )
             ( u : Forall( a1 a2 : A )( uf : { (f a1 a2) = tt } ). { a1 = a2 } )
             ( u_rfl : <br_refl_P A f> ). <eq_map A>.

             

Define eq_map_data : Fun( A : type )( e : <eq_map A> )( a1 a2 : A ). bool :=
fun( A : type )( e : <eq_map A> )( a1 a2 : A ) : bool .
  match e with
    mk_eq _ f _ _ => (f a1 a2)
  end.

        
                  
                  
                  