Include "domain.g".
Include "unary_defs.g".
Include "range_pf.g".

%-
%=== WANT
Define domain_p :=
fun( A B : type )( f : Fun( a : A ).B )( a : A )( u : Exists( b : B ).{ (f a) = b } ).
  (mk_range B B (const_fun B (f a))
-%

%FIX
Define domain_domain_P : Fun( A B : type )( f : Fun( a : A ).B )( d : < domain A B f > ).
                     <domain_P A B f (domain_data A B f d)> :=
fun( A B : type )( f : Fun( a : A ).B )( d : < domain A B f > ).
  match d with
    mk_domain _ _ _ a u =>
      (mk_fiber B B (const_f B (f a)) (domain_data A B f d) 
                existse [domain_P_pf A B f a u]
                  foralli( b : B )( u' : { (f a) = b } ).
                    existsi b { (f (domain_data A B f d)) = * }
                      trans cong (f *) hypjoin (domain_data A B f d) a by d_eq end
                            u' )
  end.


%==== if a1 = a2 and a1 is in the domain of f, then a2 is in the domain of f
Define eq_domain_P :=
fun( A B : type )( f : Fun( a : A ).B )( a1 a2 : A )( u : { a1 = a2 } )
   ( d : <domain_P A B f a1> ) : <domain_P A B f a2>.
  (domain_p A B f a2 existse [domain_P_pf A B f a1 d]
                       foralli( b : B )( u' : { (f a1) = b } ).
                         existsi b { (f a2) = * }
                                 trans cong (f *) symm u
                                       u' ).

%==== if f = g and a is in the domain of f, then a is in the domain of g
Define feq_domain_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( a : A )( d : <domain_P A B f a> ) : <domain_P A B g a>.
  (domain_p A B g a existse [domain_P_pf A B f a d]
                      foralli( b : B )( u : { (f a) = b } ).
                        existsi b { (g a) = * }
                                trans symm [feq_P_pf A B f g fe a]
                                      u ).

%==== if f = g and f is total, then g is total
Define feq_domain_total_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )
   ( fe : <feq_P A B f g> )( d : <domain_total_P A B f> ) : <domain_total_P A B g>.
  (domain_total_p A B g foralli( a : A ).
                          existse [domain_total_P_pf A B f d a]
                            foralli( b : B )( u : { (f a) = b } ).
                              existsi b { (g a) = * }
                                      trans symm [feq_P_pf A B f g fe a]
                                            u ).

%==== if f is total, then a is in the domain of f for any a
Define domain_total_domain_P :=
fun( A B : type )( f : Fun( a : A ).B )( d : <domain_total_P A B f> )( a : A ) : < domain_P A B f a >.
  (domain_p A B f a [domain_total_P_pf A B f d a]).



%==== if f and g are total, then f;g is total
Define domain_total_P_trans :=
fun( A B C : type )( f : Fun( a : A ).B )( g : Fun( b : B ). C )
   ( f_t : <domain_total_P A B f> )
   ( g_t : <domain_total_P B C g> ) : <domain_total_P A C (compose A B C f g)>.
  (domain_total_p A C (compose A B C f g)
                  foralli( a : A ).
                    existse [domain_total_P_pf A B f f_t a] 
                      foralli( b : B )( uf : { (f a) = b } ).
                        existse [domain_total_P_pf B C g g_t b]
                          foralli( c : C )( ug : { (g b) = c } ).
                            existsi c { ((compose A B C f g) a) = * }
                              trans join ((compose A B C f g) a) (g (f a))
                              trans cong (g *) uf
                                    ug ).
                  
%-
Define domain_total_P_terminates :=
fun( A B : type )( f : Fun( a : A ).B )( d : < domain_total_P A B f > )( a : A ) : B.
  match d with
    domain_total_p _ _ _ u => terminates (f a) by u
  end.
-%

                  
%==== statement domain is non-empty
%-
<domain_nempty_P A B f>
  <range_nempty_P A B f>
    <range A B f>
-%
Define type_family_abbrev domain_nempty_P := 
fun( A B : type )( f : Fun( a : A ).B ).<range A B f>.

Define domain_nempty_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( d : < domain_nempty_P A B f > ). 
                              Exists( a : A )( b : B ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( d : < domain_nempty_P A B f > ). 
  existse [range_nempty_P_pf A B f d]
    foralli( b : B )( u : Exists( a' : A ). { (f a') = b } ).
      existse u
        foralli( a : A )( u' : { (f a) = b } ).
          existsi a Exists( b' : B ).{ (f *) = b' }
            existsi b { (f a) = * }
                    u'.
                    
%==== a non-empty domain
Define type_family_abbrev domain_nempty := fun( A B : type ).<range_nempty A B>.
Define domain_nempty_data := range_nempty_data.
%Define domain_nempty_pf := range_nempty_pf.



%-
Define bf_prop :=
fun( A B : type )( f : Fun( a : A ).B )( p : Fun( A B : type )( f : Fun( a : A ).B ).type )( U : Forall( A B : type ).type )
   ( tc : Fun( A B : type )( f : Fun( a : A ).B )( u : U ).<p A B f> )
   ( C : type )( f : Fun( c : C )( a : A ).B ) : < p <pair C A> B (btu_fun C A B f) >.
  (tc <pair C A> B (btu_fun C A B f) [U <pair C A> B]).
  
  
Define mk_domain_total_bf_P :=
fun( A B C : type )( f : Fun( a : A )( b : B ).C )
   ( u : Forall( a : A )( b : B ).Exists( c : C ). { (f a b) = c } ) : <domain_total_bf_P A B C f>.
  (domain_total_p <pair A B> C (btu_fun A B C f)
                  foralli( p : <pair A B> ).
                    abbrev fstt = terminates (fst A B p) by fstTot in
                    abbrev sndt = terminates (snd A B p) by sndTot in
                    existse [u fstt sndt]
                      foralli( c : C )( u : { (f (fst A B p) (snd A B p)) = c } ).
                        existsi c { ((btu_fun A B C f) p) = * }
                        trans join ((btu_fun A B C f) p) (f (fst A B p) (snd A B p))
                              u).
  

Define domain_total_bf_P_pf :=
foralli( A B C : type )( f : Fun( a : A )( b : B ).C )( d : <domain_total_bf_P A B C f> ). 
  foralli( a : A )( b : B ).    %Exists( c : C ). { (f a b) = c }
    case d with
      domain_total_p _ _ _ u => 
        existse [u (mkpair A B a b)]
          foralli( c : C )( u' : { ((btu_fun A B C f) (mkpair A B a b)) = c } ).
            existsi c { (f a b) = * }
              trans join (f a b) ((btu_fun A B C f) (mkpair A B a b))
                    u'
    end.
-%
