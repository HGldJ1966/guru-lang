Include "homom.g".
Include "binary_defs.g".
Include "inj_map_pf.g".


%==== monomorphism preserves commutativity if f is injective and g is total
Define homom_comm_P :=
fun( A B : type )
   ( g : Fun( a1 a2 : A ).A )
   ( h : Fun( b1 b2 : B ).B )
   ( f : Fun( a : A ).B )
   ( hm : <homom_P A B g h f> )
   ( hc : <bf_comm_P B h> ) 
   ( g_t : <domain_total_P A Fun( a : A ).A g> )
   ( g_t2 : Fun( a : A ).<property A A (g a)> )

   ( fi : <inj_map_P A B f> )
   : <bf_comm_P A g>.
  (bf_comm_p A g
             foralli( a1 a2 : A ).
               abbrev ga1a2t = terminates (g a1 a2) by [domain_P_pf A A terminates (g a1) by [domain_total_P_pf A Fun( a : A ).A g g_t]
                                                                    a2 (g_tt a1 a2)] in
               abbrev ga2a1t = terminates (g a2 a1) by [domain_P_pf A A (g a2) 
                                                                    a1 (g_tt a2 a1)] in
               [inj_map_P_inj A B f fi ga1a2t ga2a1t
                 abbrev f_t = (inj_map_domain_total_P A B f fi) in
                 abbrev fa1t = terminates (f a1) by [domain_total_P_pf A B f f_t a1] in
                 abbrev fa2t = terminates (f a2) by [domain_total_P_pf A B f f_t a2] in
                 trans [homom_P_pf A B g h f hm a1 a2]
                 trans [bf_comm_P_pf B h hc fa1t fa2t]
                       symm [homom_P_pf A B g h f hm a2 a1]] ).


%-
%==== monomorphism preserves assocativity if f is injective and g is total
Define homom_assoc_P :=
fun( A B : type )
   ( g : Fun( a1 a2 : A ).A )
   ( h : Fun( b1 b2 : B ).B )
   ( f : Fun( a : A ).B )
   ( hm : <homom_P A B g h f> )
   ( ha : <bf_assoc_P B h> ) 
                                        %need to do totality of binary functions in a good way here

   ( fi : <inj_map_P A B f> )
   : <bf_assoc_P A g>.
  (bf_assoc_p A g
              foralli( a1 a2 a3 : A ).
                [inj_map_P_inj A B f fi (g a1 (g a2 a3)) (g (g a1 a2) a3)
                  abbrev f_t = (inj_map_domain_total_P A B f fi) in
                  %abbrev ga1a2t = terminates (g a1 a2) by [domain_total_P_pf A A [g_t a1] a2] in
                  %abbrev ga2a3t = terminates (g a1 a2) by [domain_total_P_pf A A [g_t a2] a3] in
                  %abbrev fa1t = terminates (f a1) by [domain_total_P_pf A B f_t a1] in
                  %abbrev fa2t = terminates (f a1) by [domain_total_P_pf A B f_t a2] in
                  %abbrev fa3t = terminates (f a1) by [domain_total_P_pf A B f_t a3] in
                  trans [homom_P_pf A B g h f hm a1 ga2a3t]
                  trans cong (h (f a1) *) [homom_P_pf A B g h f hm a2 a3]
                  trans [bf_assoc_P_pf B h ha fa1t fa2t fa3t]
                  trans cong (h * (f a3)) [homom_P_pf A B g h f hm a1 a2]
                        symm [homom_P_pf A B g h f hm ga1a2t a3] ] ).
-%
