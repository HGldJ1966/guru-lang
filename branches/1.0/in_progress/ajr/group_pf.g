Include "group.g".


Define l_identity_P_total :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( li : <l_identity_P A f e> ) : <domain_total_P A A (f e)>.
  (feq_domain_total_P A A (id_fun A) (f e) (feq_symm_P A A (f e) (id_fun A) li) (id_fun_total A)).
  
  
Define r_identity_P_total :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( ri : <r_identity_P A f e> ) : <domain_total_P A A (rev_bf A f e)>.
  (l_identity_P_total A (rev_bf A f) e ri).




%-
%====== if (A, f) forms a group and f = g, then (A, g) forms a group
Define feq_group_def_P :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( g : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( gr : <group_def_P A f e inv> )
           : <group_def_P A g e inv>.
  (group_def_p A g e
                 -%