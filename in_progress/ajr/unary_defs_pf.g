Include "unary_defs.g".
Include "domain.g".


%==== if g is the inverse of f, then f is total
Define uf_inv_domain_total_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
   ( i : < uf_inv_P A B f g > ) : <domain_total_P A B f>.
  (domain_total_p A B f
                  foralli( a : A ).
                    cinv (f a) [uf_inv_P_pf A B f g i a]).

Define uf_inv_domain_total_P_total :=
foralli( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
       ( i : < uf_inv_P A B f g > ).
  abbrev ret = (domain_total_p A B f
                               foralli( a : A ).
                                 cinv (f a) [uf_inv_P_pf A B f g i a]) in
  existsi ret { (uf_inv_domain_total_P A B f g i) = * }
    join (uf_inv_domain_total_P A B f g i) ret.
Total uf_inv_domain_total_P uf_inv_domain_total_P_total.


%===== if g is in the inverse of f and f = h, then g is the inverse of h
Define feq_uf_inv_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )( h : Fun( a : A ). B )
   ( fe : <feq_P A B f h> )( i : < uf_inv_P A B f g > ) : < uf_inv_P A B h g > .
  (uf_inv_p A B h g 
             foralli( a : A ).
               trans cong (g *) symm [feq_P_pf A B f h fe a]
                     [uf_inv_P_pf A B f g i a] ).


%===== if g is in the inverse of f and g = h, then h is the inverse of f
Define feq_uf_inv2_P : Fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )( h : Fun( b : B ). A )
                          ( fe : <feq_P B A g h> )( i : < uf_inv_P A B f g > ).< uf_inv_P A B f h > :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )( h : Fun( b : B ). A )
   ( fe : <feq_P B A g h> )( i : < uf_inv_P A B f g > ).
  (uf_inv_p A B f h  
             foralli( a : A ).
               trans symm [feq_P_pf B A g h fe terminates (f a) by cinv (f a) [uf_inv_P_pf A B f g i a] ]
                     [uf_inv_P_pf A B f g i a] ).


Define uf_inv_g_i := 
fun( A B : type )( f : Fun( a : A ).B )( i : <uf_inv A B f> ) : <uf_inv_P A B f (uf_inv_g A B f i)>.
  match i with
    mk_uf_inv _ _ _ g g_i  =>
      abbrev g_fe = (feq_p B A g (uf_inv_g A B f i)
                                     foralli( b : B ).
                                       hypjoin (g b) ((uf_inv_g A B f i) b) by i_eq end) in
      (feq_uf_inv2_P A B f g (uf_inv_g A B f i) g_fe g_i)
  end.





%-
Define uf_inv_symm_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
   ( i : < uf_inv_P A B f g > )( g_t : <domain_total_P A B g> ) : <uf_inv_P B A g f>.
  (uf_inv_p B A g f 
             foralli( b : B ).
               
               ).
-%

%-
%-
%this may require g being total
Define feq_uf_comm_P :=
fun( A B : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )( h : Fun( a : A ). A )
   ( fe : <feq_P A A f h> )( c : < uf_comm_P A f g > ) : < uf_comm_P A h g >.
  (uf_comm_p A h g 
             foralli( a : A ).
               trans cong (g *) symm [feq_P_pf A A f h fe a]
               trans [uf_comm_P_pf A f g c a]
                     [feq_P_pf A A f h fe (g a)] ).
-%   
    
                 
Define uf_comm_refl_P :=
fun( A : type )( f : Fun( a : A ).A ) : < uf_comm_P A f f >.
  ( uf_comm_p A f f foralli( a : A ).refl (f (f a)) ).


Define uf_comm_symm_P :=
fun( A : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )( c : < uf_comm_P A f g > ) : < uf_comm_P A g f >.          
  ( uf_comm_p A g f 
              foralli( a : A ).
                symm [uf_comm_P_pf A f g c a] ).


%-
Define uf_comm_trans_P : Fun( A : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )( h : Fun( a : A ). A )
                            ( c : < uf_comm_P A f g > )( c : < uf_comm_P A g h > ). < uf_comm_P A f h > :=
fun( A : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )( h : Fun( a : A ). A )
   ( c : < uf_comm_P A f g > )( c : < uf_comm_P A g h > ).        
  ( uf_comm_p A f h _ ).

-%

-%
