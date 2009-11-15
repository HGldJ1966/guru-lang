Include "../../guru-lang/lib/bool.g".
Include "range.g".
Include "equality.g".
Include "logic_defs.g".

%===== statement a is in the subset of A defined by the range of f
%-
<subset_def_P A f a>
  <fiber A A f a>
    <range_P A A f a>
-%
Define type_family_abbrev subset_def_P := fun( A : type )( f : Fun( a : A ). A )( a : A ). <fiber A A f a>.

Define subset_def_p :=
fun( A : type )( f : Fun( a : A ). A )( a a' : A )( u : { (f a') = a } ).
  (mk_fiber A A f a a' u).
  
Define subset_def_P_pf : Forall( A : type )( f : Fun( a : A ). A )( a : A )( s : <subset_def_P A f a> ).
                           Exists( a' : A ). { (f a') = a } :=
foralli( A : type )( f : Fun( a : A ). A )( a : A )( s : <subset_def_P A f a> ).
  [range_P_pf A A f a s].


%===== the subset of A defined by the range of f
%-
<subset A f>
  <range A A f>
-%
Define type_family_abbrev subset_def := fun( A : type )( f : Fun( a : A ).A ). <range A A f>. 

Define mk_subset_def :=
fun( A : type )( f : Fun( a : A ). A )( a a' : A )( u : { (f a') = a } ).
  (mk_range A A f a (subset_def_p A f a a' u)).

Define subset_def_data :=
fun( A : type )( f : Fun( a : A ). A )( s : <subset_def A f> ) : A.
  (range_data A A f s).



%==== there is a subset on type A
Define type_family_abbrev subset_P := fun( A : type ). <true_P>.


%===== subset defined on A
Inductive subset : Fun( A : type ). type :=
  mk_subset : Fun( A : type )( f : Fun( a : A ).A )( a : A )( r : <subset_def_P A f a > ).< subset A >.

Define subset_f :=
fun( A : type )( s : <subset A> )( a : A ) : A.
  match s with  
    mk_subset _ f _ _ => cast (f a) by symm inj <subset *> s_Eq
  end.

Define subset_data :=
fun( A : type )( s : <subset A> ) : A.
  match s with  
    mk_subset _ _ a _ => cast a by symm inj <subset *> s_Eq
  end.


%==== f is in the powerset of A
Define type_family_abbrev powerset_P := fun( A : type )( f : Fun( a : A ).A ). <true_P>.


%===== powerset of A
Inductive powerset : Fun( A : type ). type :=
  mk_powerset : Fun( A : type )( f : Fun( a : A ).A ).<powerset A>.

Define powerset_f :=
fun( A : type )( p : <powerset A> )( a : A ) : A.
  match p with
    mk_powerset _ f => cast (f a) by symm inj <powerset *> p_Eq
  end.


%===== restriction of f to subset A
Define restriction_fun := fun( A B : type )( f : Fun( a : A ).B )( s : <subset A> ) : B. (f (subset_data A s)).

%===== statement f is an extension of g
%-
<extension_fun_P A B g f>
  <feq_P <subset A> B (restriction_fun A B f) g>
-%
Define type_family_abbrev extension_fun_P := fun( A B : type )( g : Fun( a : <subset A> ).B )( f : Fun( a : A ).B ).
                                               <feq_P <subset A> B (restriction_fun A B f) g>.
