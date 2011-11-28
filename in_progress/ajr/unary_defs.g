Include "equality.g".
Include "fun_defs.g".

%====== statement that g is the unary inverse of f
%-
<uf_inv_P A B f g>
  <feq_P A A (compose A B A f g) (id_fun A)>
-%
Define type_family_abbrev uf_inv_P := 
fun( A B : type )( f : Fun( a : A ). B )( g : Fun( b : B ). A ). 
  <feq_P A A (compose A B A f g) (id_fun A)>.


Define uf_inv_p : Fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
                      ( u : Forall( a : A ).{ (g (f a)) = a } ).< uf_inv_P A B f g > :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )( u : Forall( a : A ).{ (g (f a)) = a } ).
  (feq_p A A (compose A B A f g) (id_fun A)
          foralli( a : A ).
            trans join ((compose A B A f g) a) (g (f a))
            trans [u a]
                  join a (id_fun A a) ).
                           

Define uf_inv_P_pf : Forall( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
                            ( i : <uf_inv_P A B f g> )( a : A ). { (g (f a)) = a } := 
foralli( A B : type )( f : Fun( a : A ).B )( g : Fun( b : B ). A )
       ( i : <uf_inv_P A B f g> )( a : A ).
  case i with
    feq_p _ _ _ _ u => trans join (g (f a)) ((compose A B A f g) a)
                        trans [u a]
                              join (id_fun A a) a
  end.
  
%================================= a unary inverse of f
Inductive uf_inv : Fun( A B : type )( f : Fun( a : A ).B ). type :=
  mk_uf_inv : Fun( A B : type )( f : Fun( a : A ).B )
                 ( g : Fun( b : B ).A )
                 ( g_i : <uf_inv_P A B f g> ). <uf_inv A B f>.


Define uf_inv_g :=
fun( A B : type )( f : Fun( a : A ).B )( i : <uf_inv A B f> )( b : B ) : A.
  match i with
    mk_uf_inv _ _ _ g _  => cast (g b) by symm inj <uf_inv * ** **> i_Eq
  end.

  
%======= statement that g commutes with f
%-
<uf_comm_P A f g>
  <feq_P A A (compose A A A f g) (compose A A A g f)>
-%
Define type_family_abbrev uf_comm_P := 
fun( A : type )( f : Fun( a : A ). A )( g : Fun( a : A ).A ).
  <feq_P A A (compose A A A f g) (compose A A A g f)>.

Define uf_comm_p :=
fun( A : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )
   ( u : Forall( a : A ). { (g (f a)) = (f (g a)) } ) : < uf_comm_P A f g >.
  (feq_p A A (compose A A A f g) (compose A A A g f)
          foralli( a : A ).
            trans join ((compose A A A f g) a) (g (f a))
            trans [u a]
                  join (f (g a)) ((compose A A A g f) a) ).

Define uf_comm_P_pf :=
foralli( A : type )( f : Fun( a : A ).A )( g : Fun( a : A ). A )
       ( c : <uf_comm_P A f g> )( a : A ).        %{ (g (f a)) = (f (g a)) }
  case c with
    feq_p _ _ _ _ u => trans join (g (f a)) ((compose A A A f g) a)
                        trans [u a]
                              join ((compose A A A g f) a) (f (g a))
  end.

