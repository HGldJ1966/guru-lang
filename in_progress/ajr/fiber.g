Include "fun_defs.g".

%===== fiber of f at b
%-
<fiber A B f b>
  <range_P A B f b>
-%
Inductive fiber : Fun( A B : type )( f : Fun( a : A ).B )( b : B ). type :=
  mk_fiber : Fun( A B : type )( f : Fun( a : A ).B )( b : B )( a : A )
                ( u : { (f a) = b } ).< fiber A B f b >.

Define fiber_data := 
fun( A B : type )( f : Fun( a : A ).B )( b : B )( e : <fiber A B f b> ) : A.
  match e with
    mk_fiber _ _ _ _ a _ => cast a by symm inj <fiber * ** ** **> e_Eq
  end.
Define fiber_data_total :=
foralli( A B : type )( f : Fun( a : A ).B )( b : B )( e : <fiber A B f b> ).
  case e with
    mk_fiber _ _ _ _ a _ =>
      existsi cast a by symm inj <fiber * ** ** **> e_Eq { (fiber_data A B f b e) = * } 
        hypjoin (fiber_data A B f b e) a by e_eq end
  end.
Total fiber_data fiber_data_total.




%===== statement that a is in the fiber of f at b
%-
<fiber_P A B f b a>
  <fiber B B (const_f B b) (f a)>
    <range_P B B (const_f B b) (f a)>
    <subset_def_P B (const_f B b) (f a)>
      <singleton_subset_def_P B b (f a)>
-%
Define type_family_abbrev fiber_P :=
fun( A B : type )( f : Fun( a : A ).B )( b : B )( a : A ). <fiber B B (const_f B b) (f a)>.


Define fiber_P_pf : Forall( A B : type )( f : Fun( a : A ). B )( b : B )( a : A )
                          ( e : <fiber_P A B f b a> ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ). B )( b : B )( a : A )( e : <fiber_P A B f b a> ).
  case e with
    mk_fiber _ _ _ _ b' u =>
      symm trans join b (const_f B b b')
           trans u
                 refl (f a)
  end.