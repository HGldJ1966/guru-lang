Include "homom.g".
Include "group.g".



%==== statement f is a group homomorphism from gp1 to gp2
Inductive gp_homom_P : Fun( A B : type )
                          ( g : Fun( a1 a2 : A ).A )    %need totality?
                          ( h : Fun( b1 b2 : B ).B )    %need totality?
                          ( g1 : <group_P A g> )
                          ( g2 : <group_P B h> )      
                          ( f : Fun( a : A ).B ). type :=
  gp_homom_p : Fun( A B : type )
                  ( g : Fun( a1 a2 : A ).A )
                  ( h : Fun( b1 b2 : B ).B )
                  ( g1 : <group_P A g> )
                  ( g2 : <group_P B h> )
                  ( f : Fun( a : A ).B )
                  ( u : <homom_P A B g h f> ). <gp_homom_P A B g h g1 g2 f>.


%==== a group homomorphism from gp1 to gp2
Inductive gp_homom : Fun( A B : type )
                        ( g : Fun( a1 a2 : A ).A )    %need totality?
                        ( h : Fun( b1 b2 : B ).B )    %need totality?
                        ( g1 : <group_P A g> )
                        ( g2 : <group_P B h> ). type :=
  mk_gp_homom : Fun( A B : type )
                   ( g : Fun( a1 a2 : A ).A )
                   ( h : Fun( b1 b2 : B ).B )
                   ( g1 : <group_P A g> )
                   ( g2 : <group_P B h> )
                   ( f : Fun( a : A ).B )
                   ( u : <homom_P A B g h f> ). <gp_homom_P A B g h g1 g2>.
              