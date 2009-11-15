Include "fun_defs.g".
Include "subset.g".

%========== statement a2 is in the singleton set a1 of A
%- 
<singleton_subset_def_P A a1 a2>
  <fiber A A (const_fun A a1) a2>
    <range_P A A (const_fun A a1) a2>
    <subset_def_P A (const_fun A a1) a2>
-%
Define type_family_abbrev singleton_subset_def_P := fun( A : type )( a1 a2 : A ). <fiber A A (bin_id_fun1 A A a1) a2>.


Define singleton_subset_def_p :=
fun( A : type )( a : A ) : <singleton_subset_def_P A a a>.
  (range_p A A (bin_id_fun1 A A a) a
           existsi a { (bin_id_fun1 A A a *) = a }
             join (bin_id_fun1 A A a a) a ).
  

Define singleton_subset_def_P_pf :=
foralli( A : type )( a1 a2 : A )( s : <singleton_subset_def_P A a1 a2> ).   %{ a1 = a2 }
  case s with
    range_p _ _ _ _ u =>  
      existse u
              foralli( a : A )( u : { (bin_id_fun1 A A a1 a) = a2 } ).
                trans join a1 (bin_id_fun1 A A a1 a)
                      u
  end.


%========== the singleton set a of A
%-
<singleton_subset_def A a>
  <range A A (const_fun A a)>
    <subset_def A (const_fun A a)>
-%
Define type_family_abbrev singleton_subset_def := fun( A : type )( a : A ). <range A A (bin_id_fun1 A A a)>.

Define mk_singleton_subset_def :=
fun( A : type )( a : A ) : <singleton_subset_def A a>.
  (mk_range A A (bin_id_fun1 A A a) a (singleton_subset_def_p A a)).
