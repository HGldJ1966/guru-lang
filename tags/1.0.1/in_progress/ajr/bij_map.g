Include "inj_map_pf.g".
Include "range_pf.g".
Include "logic_defs.g".

%=========== statement that f is bijective from A to B
%-
<bij_map_P A B f>
  <and_P <inj_map_P A B f> <range_total_P A B f> >
-%
Define type_family_abbrev bij_map_P := 
fun( A B : type )( f : Fun( a : A ).B ). <and_P <inj_map_P A B f> <range_total_P A B f> >.


Define bij_map_p := 
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )( s : <range_total_P A B f> ) : < bij_map_P A B f >.
  (and_p <inj_map_P A B f> <range_total_P A B f> i s).


Define bij_map_P_inj := 
fun( A B : type )( f : Fun( a : A ).B )( b : < bij_map_P A B f> ) : < inj_map_P A B f >.
  match b with
    and_p _ _ i _ => cast i by trans cong <inj_map_P * B f> symm inj <bij_map_P * ** **> b_Eq
                               trans cong <inj_map_P A * f> symm inj <bij_map_P ** * **> b_Eq
                                     cong <inj_map_P A B *> symm inj <bij_map_P ** ** *> b_Eq
  end.


Define bij_map_P_surj := 
fun( A B : type )( f : Fun( a : A ).B )( b : < bij_map_P A B f> ) : < range_total_P A B f >.
  match b with
    and_p _ _ _ s => cast s by trans cong <range_total_P * B f> symm inj <bij_map_P * ** **> b_Eq
                               trans cong <range_total_P A * f> symm inj <bij_map_P ** * **> b_Eq
                                     cong <range_total_P A B *> symm inj <bij_map_P ** ** *> b_Eq
  end.
  

%=========== a bijective map from A to B
Inductive bij_map : Fun( A B : type ). type :=
  mk_bij_map : Fun( A B : type )
                  ( f : Fun( a : A ).B )
                  ( b : <bij_map_P A B f> ). < bij_map A B >.


Define bij_map_f : Fun( A B : type )( b : <bij_map A B> )( a : A ). B :=
fun( A B : type )( b : <bij_map A B> )( a : A ).
  match b with
    mk_bij_map _ _ f _ => cast (f a) by symm inj <bij_map ** *> b_Eq
  end.


Define bij_map_pf : Fun( A B : type )( b : <bij_map A B> ). < bij_map_P A B (bij_map_f A B b) > :=
fun( A B : type )( b : <bij_map A B> ).
  match b with
    mk_bij_map _ _ f b' => 
      abbrev f_fe = (feq_p A B f (bij_map_f A B b)
                            foralli( a : A ).
                              hypjoin (f a) ((bij_map_f A B b) a) by b_eq end ) in  
      (bij_map_p A B (bij_map_f A B b)
                 (feq_inj_map_P A B f (bij_map_f A B b) f_fe (bij_map_P_inj A B f b'))
                 (feq_range_total_P A B f (bij_map_f A B b) f_fe (bij_map_P_surj A B f b')))
  end.


%=========== statement that f is permutation of A
%-
<permutation_P A f>
  <bij_map_P A A f>
    <and_P <inj_map_P A A f> <range_total_P A A f> >
-%
Define type_family_abbrev permutation_P := fun( A : type )( f : Fun( a : A ).A ). <bij_map_P A A f>.


%=========== a permutation of A
%-
<permutation A f>
  <bij_map A A f>
-%
Define type_family_abbrev permutation := fun( A : type ). <bij_map A A>.
