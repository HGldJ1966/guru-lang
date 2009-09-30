Include "../../guru-lang/lib/nat.g".
Include "../../guru-lang/lib/bool.g".
Include "domain.g".

%==== statement: i is an inductive mapping to the natural numbers for predecessor p and base cases pb = tt
Inductive ind_arg_P : Fun( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
                         ( i : Fun( a : A ).nat ). type :=
  ind_arg_p : Fun( A : type )
                 ( p : Fun( a : A ).A )( p_t : <domain_total_P A A p> )
                 ( pb : Fun( a : A ).bool )( pb_t : <domain_total_P A bool pb> )
                 ( i : Fun( a : A ).nat )( i_t : <domain_total_P A nat i> )
                 ( u : Forall( a : A )( n : nat )
                             ( u' : { (lt (i a) (S n)) = tt } )
                             ( ub' : { (pb a) = ff } ). { (lt (i (p a)) n) = tt } ).< ind_arg_P A p pb i>.

Define ind_arg_P_p_t :=
fun( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
   ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ) : <domain_total_P A A p>.
  match ia with
    ind_arg_p _ _ p_t _ _ _ _ _ => 
      cast p_t by trans cong <domain_total_P * A p> symm inj <ind_arg_P * ** ** **> ia_Eq
                        cong <domain_total_P A * p> symm inj <ind_arg_P * ** ** **> ia_Eq
  end.
Define ind_arg_P_p_t_total :=
foralli( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ).
  case ia with
    ind_arg_p _ _ p_t _ _ _ _ _ => 
      abbrev ret = cast p_t by trans cong <domain_total_P * A p> symm inj <ind_arg_P * ** ** **> ia_Eq
                                     cong <domain_total_P A * p> symm inj <ind_arg_P * ** ** **> ia_Eq in
      existsi ret { (ind_arg_P_p_t A p pb i ia) = * }
              hypjoin (ind_arg_P_p_t A p pb i ia) ret by ia_eq end
  end.
Total ind_arg_P_p_t ind_arg_P_p_t_total.
  
  
Define ind_arg_P_pb_t :=
fun( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
   ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ) : <domain_total_P A bool pb>.
  match ia with
    ind_arg_p _ _ _ _ pb_t _ _ _ =>
      cast pb_t by trans cong <domain_total_P * bool pb> symm inj <ind_arg_P * ** ** **> ia_Eq
                         cong <domain_total_P A bool *> symm inj <ind_arg_P ** ** * **> ia_Eq
  end.
Define ind_arg_P_pb_t_total :=
foralli( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ).
  case ia with
    ind_arg_p _ _ _ _ pb_t _ _ _ => 
      abbrev ret = cast pb_t by trans cong <domain_total_P * bool pb> symm inj <ind_arg_P * ** ** **> ia_Eq
                                      cong <domain_total_P A bool *> symm inj <ind_arg_P ** ** * **> ia_Eq in
      existsi ret { (ind_arg_P_pb_t A p pb i ia) = * }
              hypjoin (ind_arg_P_pb_t A p pb i ia) ret by ia_eq end
  end.
Total ind_arg_P_pb_t ind_arg_P_pb_t_total.


Define ind_arg_P_i_t :=
fun( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
   ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ) : <domain_total_P A nat i>.
  match ia with
    ind_arg_p _ _ _ _ _ _ i_t _ =>
      cast i_t by trans cong <domain_total_P * nat i> symm inj <ind_arg_P * ** ** **> ia_Eq
                        cong <domain_total_P A nat *> symm inj <ind_arg_P ** ** ** *> ia_Eq
  end.
Define ind_arg_P_i_t_total :=
foralli( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> ).
  case ia with
    ind_arg_p _ _ _ _ _ _ i_t _ => 
      abbrev ret = cast i_t by trans cong <domain_total_P * nat i> symm inj <ind_arg_P * ** ** **> ia_Eq
                                     cong <domain_total_P A nat *> symm inj <ind_arg_P ** ** ** *> ia_Eq in
      existsi ret { (ind_arg_P_i_t A p pb i ia) = * }
              hypjoin (ind_arg_P_i_t A p pb i ia) ret by ia_eq end
  end.
Total ind_arg_P_i_t ind_arg_P_i_t_total.


Define ind_arg_P_pf :=
foralli( A : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( i : Fun( a : A ).nat )( ia : <ind_arg_P A p pb i> )
       ( a : A )( n : nat )( u' : { (lt (i a) (S n)) = tt } )
       ( ub' : { (pb a) = ff } ).	%{ (lt (i (p a)) n) = tt } 
  case ia with
    ind_arg_p _ _ _ _ _ _ _ u => 
      trans refl (lt (i (p a)) n)
            [u a n u' ub']
  end.


%====== statement that (f a) = b is implied inductively for predecessor p and base cases pb
Inductive ind_impl_P : Fun( A B : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
                          ( f : Fun( a : A ).B )( b : B ). type :=
  ind_impl_p : Fun( A B : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
                  ( f : Fun( a : A ).B )( b : B )
                  ( ub : Forall( a : A )( u' : { (pb a) = tt } ).{ (f a) = b } )
                  ( us : Forall( a : A )
                               ( ub' : { (pb a) = ff } )
                               ( u' : { (f (p a)) = b } ). { (f a) = b } ). <ind_impl_P A B p pb f b>.
                   

Define ind_impl_P_base_pf :=
foralli( A B : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( f : Fun( a : A ).B )( b : B )( ii : <ind_impl_P A B p pb f b> )
       ( a : A )( u' : { (pb a) = tt } ).	%{(f a) = b}
  case ii with
    ind_impl_p _ _ _ _ _ _ ub _ =>
      trans refl (f a)
      trans [ub a u']
            refl b
  end.
  
Define ind_impl_P_step_pf :=
foralli( A B : type )( p : Fun( a : A ).A )( pb : Fun( a : A ).bool )
       ( f : Fun( a : A ).B )( b : B )( ii : <ind_impl_P A B p pb f b> )
       ( a : A )( ub' : { (pb a) = ff } )( u' : { (f (p a)) = b } ).		%{(f a) = b}
  case ii with
    ind_impl_p _ _ _ _ _ _ _ us =>
      trans refl (f a)
      trans [us a ub' u']
            refl b
  end.


Define ind_pf : Forall( A B : type )
                      ( p : Fun( a : A ).A )
                      ( pb : Fun( a : A ).bool )
                      ( i : Fun( a : A ).nat )
                      ( ia : <ind_arg_P A p pb i> )
                      ( f : Fun( a : A ).B )( b : B )
                      ( ii : <ind_impl_P A B p pb f b> )( a : A ). { (f a) = b } :=
foralli( A B : type )
       ( p : Fun( a : A ).A )
       ( pb : Fun( a : A ).bool )
       ( i : Fun( a : A ).nat )
       ( ia : <ind_arg_P A p pb i> )
       ( f : Fun( a : A ).B )( b : B )
       ( ii : <ind_impl_P A B p pb f b> )( a : A ).
  abbrev p_tot = (ind_arg_P_p_t A p pb i ia) in
  abbrev pb_tot = (ind_arg_P_pb_t A p pb i ia) in
  abbrev i_tot = (ind_arg_P_i_t A p pb i ia) in
  abbrev i_t = terminates (i a) by [domain_total_P_pf A nat i i_tot a] in
  [
  induction ( i_nat : nat ) by ui uI IHi return Forall( a' : A )( u : { (lt (i a') i_nat) = tt } ).
                                                  { (f a') = b } with
    Z =>
      foralli( a' : A )( u : { (lt (i a') i_nat) = tt } ).
        abbrev i_t' = terminates (i a') by [domain_total_P_pf A nat i i_tot a'] in
        contra
          trans trans symm u 
                trans cong (lt i_t' *) ui
                      [lt_Z i_t']
                clash ff tt
          { (f a') = b }
  | S i_nat' =>
      foralli( a' : A )( u : { (lt (i a') i_nat) = tt } ).
        abbrev pb_t' = terminates (pb a') by [domain_total_P_pf A bool pb pb_tot a'] in
        case pb_t' by up uP with
          ff => 
            abbrev p_t' = terminates (p a') by [domain_total_P_pf A A p p_tot a'] in
            abbrev u' = trans symm cong (lt (i a') *) ui u in
            abbrev ia' = [ind_arg_P_pf A p pb i ia a' i_nat' u' up] in
            abbrev ih' = [IHi i_nat' p_t' ia'] in
            [ind_impl_P_step_pf A B p pb f b ii a' up ih']
        | tt => [ind_impl_P_base_pf A B p pb f b ii a' up]
        end  
  end
  (S i_t) a [lt_S i_t] ].                    





%-
Define ind_arg_P_list_length :=
(ind_arg_p <list A> tail _ isnil _ length _ _).
-%
