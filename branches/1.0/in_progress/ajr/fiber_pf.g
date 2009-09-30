Include "fiber.g".
Include "fun_defs_pf.g".


%================= fiber
Define fiber_fiber_P :=
fun( A B : type )( f : Fun( a : A ). B )( b : B )( e : <fiber A B f b> ) : < fiber_P A B f b (fiber_data A B f b e)>.
  match e with
    mk_fiber _ _ _ _ a u => 
      (mk_fiber B B (const_f B b) (f (fiber_data A B f b e)) b
                symm trans cong (f *) hypjoin (fiber_data A B f b e) a by e_eq end
                     trans u
                           join b ((const_f B b) b) )
  end.

Define fiber_fiber_P_total :=
foralli( A B : type )( f : Fun( a : A ). B )( b : B )( e : <fiber A B f b> ).
  case e with
    mk_fiber _ _ _ _ a u => 
      abbrev ret = (mk_fiber B B (const_f B b) (f (fiber_data A B f b e)) b
                             symm trans cong (f *) hypjoin (fiber_data A B f b e) a by e_eq end
                                  trans u
                                        join b ((const_f B b) b) ) in
      existsi ret { (fiber_fiber_P A B f b e) = * }
        hypjoin (fiber_fiber_P A B f b e) ret by e_eq end
  end.
Total fiber_fiber_P fiber_fiber_P_total.

Define fiber_pf : Forall( A B : type )( f : Fun( a : A ). B )( b : B )
                        ( e : <fiber A B f b> ).{ (f (fiber_data A B f b e)) = b } :=
foralli( A B : type )( f : Fun( a : A ). B )( b : B )( e : <fiber A B f b> ).
  [fiber_P_pf A B f b (fiber_data A B f b e) (fiber_fiber_P A B f b e)].
  
  
%==== if b1 = b2 and b1 is in the range of f, then b2 is in the domain of f
Define eq_fiber :=
fun( A B : type )( f : Fun( a : A ).B )( b1 b2 : B )( u : { b1 = b2 } )( r : <fiber A B f b1> ) : <fiber A B f b2>.
  (mk_fiber A B f b2 (fiber_data A B f b1 r)
            trans [fiber_pf A B f b1 r]
                  u ).

%==== if f = g and b is in the range of f, then b is in the range of g
Define feq_fiber :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( b : B )( r : <fiber A B f b> ) : <fiber A B g b> .
  (mk_fiber A B g b (fiber_data A B f b r)
            trans symm [feq_P_pf A B f g fe (fiber_data A B f b r)]
                  [fiber_pf A B f b r] ).
                           
%-                  
%==== if a is in the fiber of f over b, then a is in the domain of f
Define fiber_domain_P :=
fun( A B : type )
   ( f : Fun( a : A ).B )( b : B )( a : A )
   ( e : <fiber_P A B f b a> ) : < domain_P A B f a >.
  (domain_p A B f a existsi b { (f a) = * }
                            [fiber_P_pf A B f b a e]).
               
           
%-==== 
if a1 is in the fiber of f over b1, and a2 is in the fiber of f over b2
  and hm is the homomorphism f from (A,g) to (B,h)
  then (g a1 a2) is in the fiber of f over (h b1 b2) 
=====-%
Define fiber_homom_P :=
fun( A B : type )
   ( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )
   ( f : Fun( a : A ).B )
   ( hm : <homom_P A B g h f> )
   ( b1 b2 : B )( a1 a2 : A )
   ( e1 : <fiber_P A B f b1 a1> )( e2 : <fiber_P A B f b2 a2> ) : < fiber_P A B f (h b1 b2) (g a1 a2)>.
  (fiber_p A B f (h b1 b2) (g a1 a2) trans [homom_P_pf A B g h f hm a1 a2]
                                     trans cong (h (f a1) *) [fiber_P_pf A B f b2 a2 e2]
                                           cong (h * b2) [fiber_P_pf A B f b1 a1 e1]).

Define fiber_homom :=         
fun( A B : type )
   ( g : Fun( a1 a2 : A ). A )( h : Fun( b1 b2 : B ).B )
   ( f : Fun( a : A ).B )
   ( hm : <homom_P A B g h f> )
   ( b1 b2 : B )
   ( e1 : <fiber A B f b1> )( e2 : <fiber A B f b2> ) : < fiber A B f (h b1 b2) >.
  (mk_fiber A B f (h b1 b2) (g (fiber_data A B f b1 e1) (fiber_data A B f b2 e2)) 
            (fiber_homom_P A B g h f hm b1 b2 (fiber_data A B f b1 e1) (fiber_data A B f b2 e2)
                           (fiber_pf A B f b1 e1) (fiber_pf A B f b2 e2))).
                           -%
