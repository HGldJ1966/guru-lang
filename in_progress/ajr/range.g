Include "fun_defs.g".
Include "fiber.g".

%================== predicate b is in the range of f
Define predicate range_pred :=
fun( A B : type )( f : Fun( a : A ).B )( b : B ). Exists( a : A ).{ (f a) = b }.
%================== statement b is in the range of f
%-
<range_P A B f b>
  <fiber A B f b>
-%
Define type_family_abbrev range_P :=
fun( A B : type )( f : Fun( a : A ).B )( b : B ).
  <fiber A B f b>.
     
Define range_P_witness := fiber_data.
     
Define range_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( b : B )( r : < range_P A B f b > ). 
                      Exists( a : A ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( b : B )( r : < range_P A B f b > ).
  case r with
    mk_fiber _ _ _ _ a u => 
      existsi cast a by symm inj <range_P * ** ** **> r_Eq { (f *) = b }
              u              
  end.
  
  
%================== range of f
%-
<range A B f>
  <range_nempty_P A B f>
-%
Inductive range : Fun( A B : type )( f : Fun( a : A ).B ). type :=
  mk_range : Fun( A B : type )( f : Fun( a : A ).B )( b : B )
                ( u : <range_P A B f b> ).< range A B f >.

Define range_data :=
fun( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ) : B.
  match r with
    mk_range _ _ _ b _ => cast b by symm inj <range ** * **> r_Eq
  end.
  
Define range_data_total : Forall( A B : type )( f : Fun( a : A ).B )( r : <range A B f> ). 
                            Exists( z : B ). { (range_data A B f r) = z } :=
foralli( A B : type )( f : Fun( a : A ).B )( r : <range A B f> ).
  case r with
    mk_range _ _ _ b _ => 
      existsi cast b by symm inj <range ** * **> r_Eq { (range_data A B f r) = * }
              hypjoin (range_data A B f r) b by r_eq end
  end.
Total range_data range_data_total.

  
%================== predicate that f is surjective, i.e. the range of f is equal to B
Define predicate range_total_pred :=
fun( A B : type )( f : Fun( a : A ).B ). Forall( b : B ). @<range_pred A B f b>.
%================== statement that f is surjective, i.e. the range of f is equal to B
Inductive range_total_P : Fun( A B : type )( f : Fun( a : A ).B ). type :=
  range_total_p : Fun( A B : type )( f : Fun( a : A ).B )
                     ( u : @<range_total_pred A B f> ).< range_total_P A B f >.


Define range_total_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( r : < range_total_P A B f > )( b : B ). 
                            Exists( a : A ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range_total_P A B f > )( b : B ). 
  case r with
    range_total_p _ _ _ u =>
      existse [u b]
        foralli( a : A )( u' : { (f a) = b } ).
          existsi a { (f *) = b }
                  u'              
  end.
  
Define type_family_abbrev surj_map_P := fun( A B : type )( f : Fun( a : A ).B ). <range_total_P A B f>.
  
%================== a function that is surjective from A to B
Inductive range_total : Fun( A B : type ). type :=
  mk_range_total : Fun( A B : type )( f : Fun( a : A ).B )
                      ( u : <range_total_P A B f> ).< range_total A B >.
  
Define range_total_data : Fun( A B : type )( r : < range_total A B > )( a : A ). B :=
fun( A B : type )( r : < range_total A B > )( a : A ).
  match r with
    mk_range_total _ _ f _ => cast (f a) by symm inj <range_total ** *> r_Eq
  end.

Define range_total_pf :=
fun( A B : type )( r : < range_total A B > ) : <range_total_P A B (range_total_data A B r)>.
  match r with
    mk_range_total _ _ f u => 
      (range_total_p A B (range_total_data A B r) 
                     foralli( b : B ).
                       existse [range_total_P_pf A B f u b]
                               foralli( a : A )( u' : { (f a) = b} ).
                                 existsi a { ((range_total_data A B r) *) = b }
                                         trans hypjoin ((range_total_data A B r) a) (f a) by r_eq end
                                               u' )
  end.


%================== predicate that f has a non empty range
Define predicate range_nempty_pred :=
fun( A B : type )( f : Fun( a : A ).B ). Exists( b : B ). @<range_pred A B f b>.
%================== statement that f has a non empty range
%-
<range_nempty_P A B f>
  <range A B f>
-%
Define type_family_abbrev range_nempty_P :=
fun( A B : type )( f : Fun( a : A ).B ).
  <range A B f>.
  
Define range_nempty_P_witness_r := range_data.
  
  
%================== a function that has a non empty range
Inductive range_nempty : Fun( A B : type ). type :=
  mk_range_nempty : Fun( A B : type )( f : Fun( a : A ).B )
                       ( u : <range_nempty_P A B f> ).< range_nempty A B >.
  
Define range_nempty_data : Fun( A B : type )( r : < range_nempty A B > )( a : A ). B :=
fun( A B : type )( r : < range_nempty A B > )( a : A ).
  match r with
    mk_range_nempty _ _ f _ => cast (f a) by symm inj <range_nempty ** *> r_Eq
  end.
