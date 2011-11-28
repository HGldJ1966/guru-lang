Include "fun_defs.g".
Include "logic_defs.g".
Include "bij_map.g".

%========== statement f is homomorphism from (A, g) to (B, h)
Inductive homom_P : Fun( A B : type )
                       ( g : Fun( a1 a2 : A ).A )
                       ( h : Fun( b1 b2 : B ).B )
                       ( f : Fun( a : A ).B ). type :=
  homom_p : Fun( A B : type )
               ( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )( f : Fun( a : A ). B )
               ( u : Forall( a1 a2 : A ).{ (f (g a1 a2)) = (h (f a1) (f a2)) } ). <homom_P A B g h f>.

Define homom_P_pf : Forall( A B : type )
                          ( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )( f : Fun( a : A ). B )
                          ( hm : <homom_P A B g h f> )( a1 a2 : A ).{ (f (g a1 a2)) = (h (f a1) (f a2)) } :=
foralli( A B : type )
       ( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )( f : Fun( a : A ). B )
       ( hm : <homom_P A B g h f> )( a1 a2 : A ).
  case hm with
    homom_p _ _ _ _ _ u => trans refl (f (g a1 a2))
                           trans [u a1 a2]
                                 refl (h (f a1) (f a2))
  end.
  

%========== homomorphism from (A, g) to (B, h)
Inductive homom : Fun( A B : type )( g : Fun( a1 a2 : A ).A )( h : Fun( b1 b2 : B ).B ). type :=
  mk_homom : Fun( A B : type )( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )
                ( f : Fun( a : A ). B )( u : <homom_P A B g h f> ). <homom A B g h>.


Define homom_f : Fun( A B : type )
                    ( g : Fun( a1 a2 : A ).A )( h : Fun( b1 b2 : B ).B )
                    ( hm : <homom A B g h> )( a : A ). B :=
fun( A B : type )( g : Fun( a1 a2 : A ).A )( h : Fun( b1 b2 : B ).B )
   ( hm : <homom A B g h> )( a : A ).
  match hm with
    mk_homom _ _ _ _ f _ => cast (f a) by symm inj <homom ** * ** **> hm_Eq
  end.


Define homom_pf : Fun( A B : type )
                     ( g : Fun( a1 a2 : A ).A )( h : Fun( b1 b2 : B ).B )
                     ( hm : <homom A B g h> ). <homom_P A B g h (homom_f A B g h hm)> :=
fun( A B : type )( g : Fun( a1 a2 : A ).A )( h : Fun( b1 b2 : B ).B )
   ( hm : <homom A B g h> ).
  match hm with
    mk_homom _ _ _ _ f u => 
      (homom_p A B g h (homom_f A B g h hm) 
               foralli( a1 a2 : A ).
                 trans hypjoin ((homom_f A B g h hm) (g a1 a2)) (f (g a1 a2)) by hm_eq end
                 trans [homom_P_pf A B g h f u a1 a2]
                 trans cong (h * (f a2)) hypjoin (f a1) ((homom_f A B g h hm) a1 ) by hm_eq end
                       cong (h ((homom_f A B g h hm) a1) *) hypjoin (f a2) ((homom_f A B g h hm) a2) by hm_eq end)
  end.


%===== statement f is endomorphism on (A, g)
Define type_family_abbrev endom_P := fun( A : type )
                                        ( f : Fun( a : A ).A )
                                        ( g : Fun( a1 a2 : A ).A ). <homom_P A A g g f>.

%===== endomorphism on (A, g)
Define type_family_abbrev endom := fun( A : type )
                                      ( g : Fun( a1 a2 : A ).A ). <homom A A g g>.




%===== statement f is a monomorphism from (A, g) to (B, h)
Define type_family_abbrev monom_P := fun( A B : type )
                                        ( g : Fun( a1 a2 : A ).A )
                                        ( h : Fun( b1 b2 : B ).B )
                                        ( f : Fun( a : A ).B ). < and_P <homom_P A B g h f> <inj_map_P A B f> >.
                                        
%===== monomorphism from (A, g) to (B, h)  - this requires an inductive data type
     
     
     
                            
%===== statement f is a isomorphism from (A, g) to (B, h)
Define type_family_abbrev isom_P := fun( A B : type )
                                       ( g : Fun( a1 a2 : A ).A )
                                       ( h : Fun( b1 b2 : B ).B )
                                       ( f : Fun( a : A ).B ). < and_P <homom_P A B g h f> <bij_map_P A B f> >.

%===== isomorphism from (A, g) to (B, h)  - this requires an inductive data type



%===== statement f is a epimorphism from (A, g) to (B, h)
Define type_family_abbrev epim_P := fun( A B : type )
                                       ( g : Fun( a1 a2 : A ).A )
                                       ( h : Fun( b1 b2 : B ).B )
                                       ( f : Fun( a : A ).B ). < and_P <homom_P A B g h f> <range_total_P A B f> >.
                                        
%===== epimorphism from (A, g) to (B, h)  - this requires an inductive data type



%===== statement f is an automorphism on (A, g)
Define type_family_abbrev autom_P := fun( A : type )
                                        ( f : Fun( a : A ).A )
                                        ( g : Fun( a1 a2 : A ).A ). < and_P <homom_P A A g g f> <isom_P A A g g f> >.

%============ automorphism on (A, g)   - this requires an inductive data type



















%-  unary homomorphism??
Define type_family_abbrev uhomom_P := fun( A B : type )( f : Fun( a : A ). B )( g : Fun( a : A ). A )( h : Fun( b : B ).B ).
                                        <f_eq A B (compose A B B f h) (compose A A B g f)>.
                                       

Define utb : Fun( A B : type )( f : Fun( a : A ).B )( a1 a2 : A ). B :=
fun( A B : type )( f : Fun( a : A ).B )( a1 a2 : A ).
  (f a1).

Define type_family_abbrev uhomom_P := fun( A B : type )( f : Fun( a : A ). B )( g : Fun( a : A ). A )( h : Fun( b : B ).B ).
                                        <homom_P A B f (utb A A g) (utb B B h)>.                                 
-%




%-
Define apply_inj_map_hom : Fun( A B : type )( h : <homom A B> )( i : <inj_map A B> )( a : A ). A :=

-%



%(mk_homomorphism <list A> nat length append plus ...)

%-

fun( A : type )( n : nat )( v : <vec A n> ) : <homom <list A> nat>.
  (mk_homom <list A> nat length (append v) (plus (length v)) ... )

-%
