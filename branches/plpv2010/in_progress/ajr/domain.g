Include "fun_defs.g".
Include "../../guru-lang/lib/nat.g".
Include "range.g".

%==================== predicate a is in the domain of f
Define predicate domain_pred := 
fun( A B : type )( f : Fun( a : A ).B )( a : A ). Exists( b : B ).{ (f a) = b }.
%==================== statement a is in the domain of f
%-
Inductive domain_P : Fun( A B : type )( f : Fun( a : A ).B )( a : A ). type :=
  domain_p : Fun( A B : type )( f : Fun( a : A ).B )( a : A )
                ( u : Exists( b : B ).{ (f a) = b } ).< domain_P A B f a >.
                
Define domain_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( a : A )( d : < domain_P A B f a > ). 
                       Exists( b : B ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( a : A )( d : < domain_P A B f a > ).
  case d with
    domain_p _ _ _ _ u => 
      existse u
        foralli( b : B )( u' : { (f a) = b } ).
          existsi b { (f a) = * }
                  u'             
  end.
-%


%-
<domain_P A B f a>
  <range B B (const_fun B (f a))>
    <range_nempty_P B B (const_f B (f a))>
-%
Define type_family_abbrev domain_P :=
fun( A B : type )( f : Fun( a : A ).B )( a : A ).
  <range B B (const_f B (f a))>.

Define domain_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( a : A )( d : < domain_P A B f a > ). 
                       Exists( b : B ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( a : A )( d : < domain_P A B f a > ).
  case d with
    mk_range _ _ _ _ u => 
      case u with
        mk_fiber _ _ _ b b' u' =>
          existsi cast b by symm inj <fiber ** * ** **> u_Eq { (f a) = * }
            trans join (f a) (const_f B (f a) b')
                  u'
      end
  end.


%=================== domain of f
Inductive domain : Fun( A B : type )( f : Fun( a : A ).B ). type :=
  mk_domain : Fun( A B : type )( f : Fun( a : A ).B )( a : A )
                 ( u : <domain_P A B f a> ).< domain A B f >.

Define domain_data : Fun( A B : type )( f : Fun( a : A ).B )( d : < domain A B f > ). A :=
fun( A B : type )( f : Fun( a : A ).B )( d : < domain A B f > ).
  match d with
    mk_domain _ _ _ a _ => cast a by symm inj <domain * ** **> d_Eq
  end.
Define domain_data_total : Forall( A B : type )( f : Fun( a : A ).B )( d : <domain A B f> ). 
                             Exists( z : A ). { (domain_data A B f d) = z } :=
foralli( A B : type )( f : Fun( a : A ).B )( d : <domain A B f> ).
  case d with
    mk_domain _ _ _ a _ => 
      existsi cast a by symm inj <domain * ** **> d_Eq { (domain_data A B f d) = * }
              hypjoin (domain_data A B f d) a by d_eq end
  end.
Total domain_data domain_data_total.

%================== predicate that f is total, i.e. the domain of f is equal to A
Define predicate domain_total_pred := 
fun( A B : type )( f : Fun( a : A ).B ). Forall( a : A ). @<domain_pred A B f a>.
%================== statement that f is total, i.e. the domain of f is equal to A
Inductive domain_total_P : Fun( A B : type )( f : Fun( a : A ).B ). type :=
  domain_total_p : Fun( A B : type )( f : Fun( a : A ).B )
                      ( u : Forall( a : A ).Exists( b : B ).{ (f a) = b } ).< domain_total_P A B f >.


Define domain_total_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( d : < domain_total_P A B f > )( a : A ). 
                             Exists( b : B ). { (f a) = b } :=
foralli( A B : type )( f : Fun( a : A ).B )( d : < domain_total_P A B f > )( a : A ). 
  case d with
    domain_total_p _ _ _ u => 
      existse [u a]
        foralli( b : B )( u' : { (f a) = b } ).
          existsi b { (f a) = * }
                  trans u' 
                        refl b               
  end.


%================== a function that is total from A to B
Inductive domain_total : Fun( A B : type ). type :=
  mk_domain_total : Fun( A B : type )( f : Fun( a : A ).B )
                       ( u : <domain_total_P A B f> ).< domain_total A B >.
  
Define domain_total_data : Fun( A B : type )( d : < domain_total A B > )( a : A ). B :=
fun( A B : type )( d : < domain_total A B > )( a : A ).
  match d with
    mk_domain_total _ _ f _ => cast (f a) by symm inj <domain_total ** *> d_Eq
  end.

Define domain_total_pf : Fun( A B : type )( d : < domain_total A B > ).
                           <domain_total_P A B (domain_total_data A B d)> :=
fun( A B : type )( d : < domain_total A B > ).
  match d with
    mk_domain_total _ _ f u => 
      (domain_total_p A B (domain_total_data A B d) 
                      foralli( a : A ).
                        existse [domain_total_P_pf A B f u a]
                                foralli( b : B )( u' : { (f a) = b} ).
                                  existsi b { ((domain_total_data A B d) a) = * }
                                          trans hypjoin ((domain_total_data A B d) a) (f a) by d_eq end
                                                u' )       
  end.
  
  
%==== for domain non-empty, see domain_pf.g 
  
  
%=====
Define type_family_abbrev null_domain_P := fun( A B : type ). <domain A B (null_fun A B)>.




%==================== statement (a,b) is in the domain of f
Inductive domain_bf_P : Fun( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B ). type :=
  domain_bf_p : Fun( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B )
                   ( u : Exists( c : C ).{ (f a b) = c } ).< domain_bf_P A B C f a b >.
                
Define domain_bf_P_pf : Forall( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B )( d : < domain_bf_P A B C f a b > ). 
                          Exists( c : C ). { (f a b) = c } :=
foralli( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B )( d : < domain_bf_P A B C f a b > ).
  case d with
    domain_bf_p _ _ _ _ _ _ u => 
      existse u
        foralli( c : C )( u' : { (f a b) = c } ).
          existsi c { (f a b) = * }
                  u'             
  end.
%-
Define domain_bf_P_domain_P :=
fun( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B )( d : < domain_bf_P A B C f a b > ) : < domain_P B C (f a) b>.
  (domain_p B C (f a) b [domain_bf_P_pf A B C f a b d]).
-%

%=================== domain of f
Inductive domain_bf : Fun( A B C : type )( f : Fun( a : A )( b : B ).C ). type :=
  mk_domain_bf : Fun( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B )
                    ( u : <domain_bf_P A B C f a b> ).< domain_bf A B C f >.


















%-
%================== statement that f is total, i.e. the domain of f is equal to AxB
Define type_family_abbrev domain_bf_P :=
fun( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B ).
  <domain_P <pair A B> C (btu_fun A B C f) (mkpair A B a b)>.


%================== statement that f is total, i.e. the domain of f is equal to AxB
Define type_family_abbrev domain_total_bf_P :=
fun( A B C : type )( f : Fun( a : A )( b : B ).C ).
  <domain_total_P <pair A B> C (btu_fun A B C f)>.
-%