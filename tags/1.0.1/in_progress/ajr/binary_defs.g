
%======== statement f is equal to b on the diagonal
Inductive bf_diag_P : Fun( A B : type )( b : B )( f : Fun( a1 a2 : A ).B ). type :=
  bf_diag_p : Fun( A B : type )( b : B )( f : Fun( a1 a2 : A ).B )
                 ( u : Forall( a : A ).{ (f a a) = b } ). <bf_diag_P A B b f>.
                 
Define bf_diag_P_pf :=
foralli( A B : type )( b : B )( f : Fun( a1 a2 : A ).B )
       ( bfd : <bf_diag_P A B b f> )( a : A ).        %{ (f a a) = b }
  case bfd with     
    bf_diag_p _ _ _ _ u => trans refl (f a a)
                           trans [u a]
                                 refl b
  end.

%======== function that equals b on the diagonal
Inductive bf_diag : Fun( A B : type )( b : B ). type :=
  mk_bf_diag : Fun( A B : type )( b : B )( f : Fun( a1 a2 : A ).B )
                  ( u : <bf_diag_P A B b f> ). <bf_diag A B b>.

Define bf_diag_data :=
fun( A B : type )( b : B )( bfd : <bf_diag A B b> )( a1 a2 : A ) : B.
  match bfd with
    mk_bf_diag _ _ _ f _ => cast (f a1 a2) by symm inj <bf_diag ** * **> bfd_Eq
  end.


%========= statement f is commutative
Inductive bf_comm_P : Fun( A B : type )( f : Fun( a1 a2 : A ).B ). type :=
  bf_comm_p : Fun( A B : type )( f : Fun( a1 a2 : A ).B )
                 ( u : Forall( a1 a2 : A ). { (f a1 a2) = (f a2 a1) } ). <bf_comm_P A B f>.
                     
Define bf_comm_P_pf :=
foralli( A B : type )( f : Fun( a1 a2 : A ).B )( bfc : <bf_comm_P A B f> )
       ( a1 a2 : A ).     %{ (f a1 a2) = (f a2 a1) }
  case bfc with
    bf_comm_p _ _ _ u => trans refl (f a1 a2)
                         trans [u a1 a2]
                               refl (f a2 a1)
  end.

%========= function that is commutative
Inductive bf_comm : Fun( A B : type ). type :=
  mk_bf_comm : Fun( A B : type )( f : Fun( a1 a2 : A ).B )
                  ( u : <bf_comm_P A B f> ). <bf_comm A B>.

Define bf_comm_data :=
fun( A B : type )( bfc : <bf_comm A B> )( a1 a2 : A ) : B.
  match bfc with
    mk_bf_comm _ _ f _ => cast (f a1 a2) by symm inj <bf_comm ** *> bfc_Eq
  end.


%========= statement f is associative
Inductive bf_assoc_P : Fun( A : type )( f : Fun( a1 a2 : A ).A ). type :=
  bf_assoc_p : Fun( A : type )( f : Fun( a1 a2 : A ).A )
                  ( u : Forall( a1 a2 a3 : A ). { (f (f a1 a2) a3) = (f a1 (f a2 a3)) } ). <bf_assoc_P A f>.
                     
Define bf_assoc_P_pf :=
foralli( A : type )( f : Fun( a1 a2 : A ).A )( bfa : <bf_assoc_P A f> )
       ( a1 a2 a3 : A ).      %{ (f (f a1 a2) a3) = (f a1 (f a2 a3)) }
  case bfa with
    bf_assoc_p _ _ u => trans refl (f (f a1 a2) a3)
                        trans [u a1 a2 a3]
                              refl (f a1 (f a2 a3))
  end.
  
%========= function that is associative
Inductive bf_assoc : Fun( A : type ). type :=
  mk_bf_assoc : Fun( A : type )( f : Fun( a1 a2 : A ).A )
                   ( u : <bf_assoc_P A f> ). <bf_assoc A>.
                  
                  