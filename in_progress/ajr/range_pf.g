Include "range.g".
Include "unary_defs.g".
Include "fiber_pf.g".

%================ range_P
%- *** WANT
Define range_p :=
fun( A B : type )( f : Fun( a : A ).B )( b : B )
   ( u : Exists( a : A ).{ (f a) = b } ) : < range_P A B f b >.
-%
%==== if b1 = b2 and b1 is in the range of f, then b2 is in the domain of f
Define eq_range_P := eq_fiber.
%==== if f = g and b is in the range of f, then b is in the range of g
Define feq_range_P := feq_fiber.
                  
                  
%================ range
Define range_range_P : Fun( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ). <range_P A B f (range_data A B f r)> :=
fun( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  match r with
    mk_range _ _ _ b u => 
      (mk_fiber A B f (range_data A B f r) (fiber_data A B f b u)
                trans [fiber_pf A B f b u]
                      hypjoin b (range_data A B f r) by r_eq end )
  end.
Define range_range_P_total :=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  case r with
    mk_range _ _ _ b u => 
      abbrev ret = (mk_fiber A B f (range_data A B f r) (fiber_data A B f b u)
                             trans [fiber_pf A B f b u]
                                   hypjoin b (range_data A B f r) by r_eq end ) in
      existsi ret { (range_range_P A B f r) = * }
              hypjoin (range_range_P A B f r) ret by r_eq end
  end.
Total range_range_P range_range_P_total.


Define range_pf : Forall( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ). 
                    Exists( a : A ).{ (f a) = (range_data A B f r) }:=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  [range_P_pf A B f (range_data A B f r) (range_range_P A B f r)].
  
  
Define range_witness :=
fun( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  (fiber_data A B f (range_data A B f r) (range_range_P A B f r)).
Define range_witness_total :=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  abbrev ret = (fiber_data A B f (range_data A B f r) (range_range_P A B f r)) in
  existsi ret { (range_witness A B f r) = * }
         join (range_witness A B f r) ret.
Total range_witness range_witness_total.
  
  
Define range_fiber_pf : Forall( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ). 
                          { (f (range_witness A B f r)) = (range_data A B f r) }:=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range A B f > ).
  trans cong (f *) join (range_witness A B f r) (fiber_data A B f (range_data A B f r) (range_range_P A B f r))
        [fiber_pf A B f (range_data A B f r) (range_range_P A B f r)].
        
        
%==== if f = g and there exists an object in range of f, then there exists an object in range of g
Define feq_range := 
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( r : <range A B f> ) : <range A B g>.
  (mk_range A B g (range_data A B f r)
            (feq_range_P A B f g fe (range_data A B f r) (range_range_P A B f r))).
        
        
        
%====================range_total_P

%==== if f = g and f is surjective, then g is surjective
Define feq_range_total_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( r : <range_total_P A B f> ) : <range_total_P A B g> .
  (range_total_p A B g foralli( b : B ).
                         existse [range_total_P_pf A B f r b]
                           foralli( a : A )( u : { (f a) = b } ).
                             existsi a { (g *) = b }
                                     trans symm [feq_P_pf A B f g fe a]
                                           u ).
                                           
%=== if f is surjective, then b is in the range of f for any b.
%- *** WANT
Define range_total_range_P :=
fun( A B : type )( f : Fun( a : A ).B )( r : <range_total_P A B f> )( b : B ) : < range_P A B f b > .
  (mk_fiber A B f b [range_total_P_pf A B f r b]).
-%

%=== if f is surjective and there exists an object in B, then f has a non-empty range
%- *** WANT
Define range_total_range_nempty_P :=
fun( A B : type )( f : Fun( a : A ).B )( r : <range_total_P A B f> )( b : B ) : < range_nempty_P A B f > .
  (mk_range A B f b (range_total_P_range_P A B f r b)).                  
-%

%=== if f and g are surjective, then f;g is surjective
Define range_total_P_trans :=
fun( A B C : type )( f : Fun( a : A ).B )( g : Fun( b : B ). C )
   ( f_t : <range_total_P A B f> )( g_t : <range_total_P B C g> ) : <range_total_P A C (compose A B C f g)>.
  (range_total_p A C (compose A B C f g)
                 foralli( c : C ).
                   existse [range_total_P_pf B C g g_t c] 
                     foralli( b : B )( ug : { (g b) = c } ).
                       existse [range_total_P_pf A B f f_t b]
                         foralli( a : A )( uf : { (f a) = b } ).
                           existsi a { ((compose A B C f g) *) = c }
                             trans join ((compose A B C f g) a) (g (f a))
                             trans cong (g *) uf
                                   ug ).
                                   

%=== if g is the uf_inv of f, then g is surjective
Define uf_inv_range_total_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ).A )
   ( i : <uf_inv_P A B f g> ) : <range_total_P B A g>.
  (range_total_p B A g
                 foralli( a : A ).
                   existsi terminates (f a) by cinv (f a) [uf_inv_P_pf A B f g i a] { (g *) = a }
                           [uf_inv_P_pf A B f g i a] ).


%================== range_nempty_P
%- *** WANT
Define range_nempty_p :=
fun( A B : type )( f : Fun( a : A ).B )
   ( u : @<range_nempty_pred A B f> ) : < range_nempty_P A B f >.
-%

Define range_nempty_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( r : < range_nempty_P A B f > ). 
                             Exists( b : B )( a : A ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( r : < range_nempty_P A B f > ). 
  case r with
    mk_range _ _ _ b u => 
      existsi (range_data A B f r) Exists( a' : A ).{ (f a') = * }
        existsi (range_witness A B f r) { (f *) = (range_data A B f r) }
                [range_fiber_pf A B f r]
  end.
  
Define range_nempty_P_witness_d := range_witness.
Define range_nempty_P_fiber_pf := range_fiber_pf.
Define feq_range_nempty_P := feq_range.

  
%================== range_nempty
Define range_nempty_range_nempty_P :=
fun( A B : type )( r : < range_nempty A B > ) : <range_nempty_P A B (range_nempty_data A B r)>.
  match r with
    mk_range_nempty _ _ f u => 
      abbrev rndf = (feq_p A B f (range_nempty_data A B r) 
                           foralli( a : A ).
                             hypjoin (f a) ((range_nempty_data A B r) a) by r_eq end) in
      (mk_range A B (range_nempty_data A B r) (range_nempty_P_witness_r A B f u)
                (feq_range_P A B f (range_nempty_data A B r) rndf (range_nempty_P_witness_r A B f u) (range_range_P A B f u)))
  end.

