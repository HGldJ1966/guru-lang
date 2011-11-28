Include "../../guru-lang/lib/bool.g".
Include "logic_defs.g".
Include "binary_defs.g".

%======== statement f is a reflexive binary relation
Define type_family_abbrev br_refl_P :=
fun( A : type )( f : Fun( a1 a2 : A ).bool ).
  <bf_diag_P A bool tt f>.
                 
Define br_refl_P_pf := bf_diag_P_pf.

%======== a refl binary relation
Define type_family_abbrev br_refl :=
fun( A : type ).
  <bf_diag A bool tt>.
              
Define br_refl_data := bf_diag_data.


%======== statement f is a symmetric binary relation
Define type_family_abbrev br_symm_P :=
fun( A : type )( f : Fun( a1 a2 : A ).bool ). 
  <bf_comm_P A bool f>.

Define br_symm_P_pf := bf_comm_P_pf.

%======== a symm binary relation
Define type_family_abbrev br_symm :=
fun( A : type ).
  <bf_comm A bool>.

Define br_symm_data := bf_comm_data.

                 
%======== statement f is a transitive binary relation       
Inductive br_trans_P : Fun( A : type )( f : Fun( a1 a2 : A ).bool ). type :=
  br_trans_p : Fun( A : type )( f : Fun( a1 a2 : A ).bool )
                  ( u : Forall( a1 a2 a3 : A )
                              ( u1 : { (f a1 a2) = tt } )
                              ( u2 : { (f a2 a3) = tt } ).{ (f a1 a3) = tt } ). <br_trans_P A f>.         
               
  
Define br_trans_P_pf : Forall( A : type )( f : Fun( a1 a2 : A ).bool )( brr : <br_trans_P A f> )
                             ( a1 a2 a3 : A )( u1 : { (f a1 a2) = tt } )( u2 : { (f a2 a3) = tt } ).{ (f a1 a3) = tt } :=
foralli( A : type )( f : Fun( a1 a2 : A ).bool )( brr : <br_trans_P A f> )
       ( a1 a2 a3 : A )( u1 : { (f a1 a2) = tt } )( u2 : { (f a2 a3) = tt } ).
  case brr with     
    br_trans_p _ _ u' => trans refl (f a1 a3)
                               [u' a1 a2 a3 u1 u2]
  end.

%======== a trans binary relation
Inductive br_trans : Fun( A : type ). type :=
  mk_br_trans : Fun( A : type )( f : Fun( a1 a2 : A ).bool )
                   ( u : <br_trans_P A f> ). <br_trans A>.
                 
Define br_trans_data :=
fun( A : type )( br : <br_trans A> )( a1 a2 : A ) : bool.
  match br with
    mk_br_trans _ f _ => (f a1 a2)
  end.

%======== the statement f forms an equivalence relation on A
Define type_family_abbrev equiv_rel_P := 
fun( A : type )( f : Fun( a1 a2 : A ).bool ).
  <and_P <br_refl_P A f> <and_P <br_symm_P A f> <br_trans_P A f> > >.

Define equiv_rel_refl :=
fun( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> ) : <br_refl_P A f>.
  match er with
    and_p _ _ r _ => cast r by trans cong <br_refl_P * f> symm inj <equiv_rel_P * **> er_Eq
                               			 cong <br_refl_P A *> symm inj <equiv_rel_P ** *> er_Eq
  end.

Define equiv_rel_symm :=
fun( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> ) : <br_symm_P A f>.
  match er with
    and_p _ _ _ er' => 
      match er' with
        and_p _ _ s _ => cast s by trans cong <br_symm_P * f> symm inj <equiv_rel_P * **> er_Eq
                                    		 cong <br_symm_P A *> symm inj <equiv_rel_P ** *> er_Eq
      end
  end.

Define equiv_rel_trans :=
fun( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> ) : <br_trans_P A f>.
  match er with
    and_p _ _ _ er' => 
      match er' with
        and_p _ _ _ t => cast t by trans cong <br_trans_P * f> symm inj <equiv_rel_P * **> er_Eq
                                         cong <br_trans_P A *> symm inj <equiv_rel_P ** *> er_Eq
      end
  end.

%======== an equivalence relation on A
Inductive equiv_rel : Fun( A : type ).type :=
  mk_equiv_rel : Fun( A : type )( f : Fun( a1 a2 : A ).bool )
                    ( ur : <equiv_rel_P A f> ).<equiv_rel A>.

Define equiv_rel_f :=
fun( A : type )( er : <equiv_rel A> )( a1 a2 : A ) : bool.
  match er with
    mk_equiv_rel _ f _ => (f a1 a2)
  end.


%====== the equivalence class of er for a in A
Inductive equiv_class : Fun( A : type )( f : Fun( a1 a2 : A ).bool )
                           ( er : <equiv_rel_P A f> )( a : A ). type :=
  mk_equiv_class : Fun( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> )( a : A )
                      ( a1 : A )( u : { (f a a1) = tt } ). < equiv_class A f er a >.
                      
Define equiv_class_data :=
fun( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> )( a : A )( ec : <equiv_class A f er a> ).
  match ec with
    mk_equiv_class _ _ _ _ a1 _ => cast a1 by symm inj <equiv_class * ** ** **> ec_Eq
  end.
  
Define equiv_class_pf : Forall( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> )( a : A )
                              ( ec : <equiv_class A f er a> ). { (f a (equiv_class_data A f er a ec)) = tt } :=
foralli( A : type )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel_P A f> )( a : A )
       ( ec : <equiv_class A f er a> ).
  case ec with
    mk_equiv_class _ _ _ _ a1 u => trans cong (f a *) hypjoin (equiv_class_data A f er a ec) a1 by ec_eq end
                                         u
  end.
  
  
%==== a partition of A
%-
Inductive partition : Fun( A : type )( a : A ). type :=
  mk_partition : Fun( A : type )( a : A )( f : Fun( a1 a2 : A ).bool )( er : <equiv_rel A f> )
                    ( u : { (f a a1) = tt } ).
-%           
