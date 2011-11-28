Include "inj_map.g".
Include "domain_pf.g".
Include "unary_defs_pf.g".


Define inj_map_P_g_i := 
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> ) : <uf_inv_P A B f (inj_map_P_g A B f i)>.
  match i with
    mk_uf_inv _ _ _ g g_i  =>
      abbrev g_fe = (feq_p B A (uf_inv_g A B f i) (inj_map_P_g A B f i)
                                     foralli( b : B ).
                                       hypjoin ((uf_inv_g A B f i) b) ((inj_map_P_g A B f i) b) by i_eq end) in
      (feq_uf_inv2_P A B f (uf_inv_g A B f i) (inj_map_P_g A B f i) g_fe (uf_inv_g_i A B f i))
  end.
  

Define inj_map_pf :=
fun( A B : type )( i : <inj_map A B> ): <inj_map_P A B (inj_map_f A B i)>.
  match i with
    mk_inj_map _ _ f u => 
      match u with
        mk_uf_inv _ _ _ g g_i =>
          abbrev f_fe = (feq_p A B f (inj_map_f A B i)
                                foralli( a : A ).
                                  hypjoin (f a) ((inj_map_f A B i) a) by i_eq end ) in
          abbrev g_fe = (feq_p B A g (inj_map_P_g A B f u)
                                foralli( b : B ).
                                  hypjoin (g b) ((inj_map_P_g A B f u) b) by u_eq end ) in                   
          (inj_map_p A B (inj_map_f A B i) (inj_map_P_g A B f u) 
                         (feq_uf_inv_P A B f (inj_map_P_g A B f u) (inj_map_f A B i) f_fe
                                         (feq_uf_inv2_P A B f g (inj_map_P_g A B f u) g_fe g_i)))
      end
  end. 

Define inj_map_g :=
fun( A B : type )( i : <inj_map A B> )( b : B ) : A.
  (inj_map_P_g A B (inj_map_f A B i) (inj_map_pf A B i) b).



%==== if f = g and f is injective, then g is injective
Define feq_inj_map_P  :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( i : <inj_map_P A B f> ) : <inj_map_P A B g>.
  match i with
    mk_uf_inv _ _ _ g' g_i'  => 
      (inj_map_p A B g g' (feq_uf_inv_P A B f g' g fe g_i'))
  end.
       

%==== if f is injective, then f is total
Define inj_map_domain_total_P :=
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> ) : <domain_total_P A B f>.
  match i with
    mk_uf_inv _ _ _ g g_i => (uf_inv_domain_total_P A B f g g_i)
  end.

Define inj_map_domain_total_P_total :=
foralli( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> ).
  case i with
    mk_uf_inv _ _ _ g g_i => 
      existsi (uf_inv_domain_total_P A B f g g_i) { (inj_map_domain_total_P A B f i) = * }
        hypjoin (inj_map_domain_total_P A B f i) (uf_inv_domain_total_P A B f g g_i) by i_eq end
  end.
Total inj_map_domain_total_P inj_map_domain_total_P_total.

%==== injective map inj rule
Define inj_map_P_inj : Forall( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )
                             ( a1 a2 : A )( u : { (f a1) = (f a2) } ).{ a1 = a2 } :=
foralli( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )
       ( a1 a2 : A )( u : { (f a1) = (f a2) } ).
  case i with
    mk_uf_inv _ _ _ g g_i =>
      trans symm [uf_inv_P_pf A B f g g_i a1]
      trans cong (g *) u
            [uf_inv_P_pf A B f g g_i a2]
  end.
  
  
  

%==== if f1 and f2 are injective, then f1;f2 is injective
Define inj_map_P_trans :=
fun( A B C : type )( f1 : Fun( a : A ).B )( f2 : Fun( b : B ).C )
   ( i1 : <inj_map_P A B f1> )( i2 : <inj_map_P B C f2> ) : <inj_map_P A C (compose A B C f1 f2)>.
  match i1 with
    mk_uf_inv _ _ _ g1 g1_i =>
      match i2 with
        mk_uf_inv _ _ _ g2 g2_i =>
          (inj_map_p A C (compose A B C f1 f2) (compose C B A g2 g1)
                     (uf_inv_p A C (compose A B C f1 f2) (compose C B A g2 g1)
                                foralli( a : A ).
                                  trans join ((compose C B A g2 g1) ((compose A B C f1 f2) a)) (g1 (g2 (f2 (f1 a))))
                                  trans cong (g1 *) [uf_inv_P_pf B C f2 g2 g2_i 
                                                                  terminates (f1 a) by cinv (f1 a) [uf_inv_P_pf A B f1 g1 g1_i a] ]
                                                    [uf_inv_P_pf A B f1 g1 g1_i a] ))
      end
  end.



%==== unary function conversion
Define inj_map_P_uf :=
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )( h : Fun( b : B ).B )( a : A ) : A.
  (inj_map_P_g A B f i (h (f a))).

%==== binary function conversion
Define inj_map_P_bf :=
fun( A B : type )( f : Fun( a : A ).B )( i : <inj_map_P A B f> )( h : Fun( b1 b2 : B ).B )( a1 a2 : A ) : A.
  (inj_map_P_g A B f i (h (f a1) (f a2))).
