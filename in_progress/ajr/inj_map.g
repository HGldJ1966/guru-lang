Include "unary_defs.g".
Include "domain.g".


%================================= statement that f is injective from A to B
%-
<inj_map_P A B f>
  <uf_inv A B f>        %existence of an inverse implies f is injective
-%
Define type_family_abbrev inj_map_P := fun( A B : type )( f : Fun( a : A ).B ).<uf_inv A B f>.

Define inj_map_p := mk_uf_inv.

Define inj_map_P_g :=
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )( b : B ) : A.
  (uf_inv_g A B f i b).

%==================== an injective map from A to B
Inductive inj_map : Fun( A B : type ). type :=
  mk_inj_map : Fun( A B : type )( f : Fun( a : A ).B )
                  ( u : <inj_map_P A B f> ). < inj_map A B >.

Define inj_map_f :=
fun( A B : type )( i : <inj_map A B> )( a : A ) : B.
  match i with
    mk_inj_map _ _ f _ => cast (f a) by symm inj <inj_map ** *> i_Eq
  end.
  
  
%-
Define inj_map_g_i := 
fun( A B : type )( i : <inj_map A B> ) : <uf_inv_P A B (inj_map_f A B i) (inj_map_g A B i)>.
  match i with
    mk_inj_map _ _ f u  =>
      abbrev g_fe = (feq_p B A (inj_map_g A B i) (inj_map_P_g A B f u)
                            foralli( b : B ).
                              hypjoin ((inj_map_g A B i) b) ((inj_map_P_g A B f u) b) by i_eq end) in
      (feq_uf_inv2_P A B (inj_map_f A B i) (inj_map_g A B i) (inj_map_P_g A B f u) g_fe
                       (inj_map_P_g_i A B (inj_map_f A B i) (inj_map_pf A B i)))
  end.
-%

