Include "binary_defs.g".
Include "logic_defs.g".
Include "equality_pf.g".
Include "fun_defs_pf.g".
Include "domain_pf.g".

%===== statement that e is a left identity w.r.t. (A, f)
%-
<l_identity_P A f e>
  <feq_P A A (f e) (id_fun A)>
-%
Define type_family_abbrev l_identity_P := 
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A ).<feq_P A A (f e) (id_fun A)>.

Define l_identity_p :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( u : Forall( a : A ).{ (f e a) = a } ).
  (feq_p A A (f e) (id_fun A) 
         foralli( a : A ).
           trans [u a]
                 join a (id_fun A a) ).
                 
Define l_identity_P_pf :=
foralli( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( li : <l_identity_P A f e> ).  %  Forall( a : A ).{ (f e a) = a }
  foralli( a : A ).
    case li with
      feq_p _ _ _ _ u => trans refl ((f e) a)
                         trans [u a]
                               join (id_fun A a) a
    end.  
    

%===== statement that e is a right identity w.r.t. (A, f)
%-
<r_identity_P A f e>
  <feq_P A A (rev_f A f e) (id_fun A)>
    <l_identity A (rev_f A f) e>
-%
Define type_family_abbrev r_identity_P := 
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A ). <feq_P A A (rev_f A f e) (id_fun A)>.





Define r_identity_p :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( u : Forall( a : A ).{ (f a e) = a } ).
  (l_identity_p A (rev_f A f) e 
                foralli( a : A ).
                  trans join ((rev_f A f e) a) (f a e)
                        [u a]).
                 
Define r_identity_P_pf :=
foralli( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( ri : <r_identity_P A f e> ).  %  Forall( a : A ).{ (f a e) = a }
  foralli( a : A ).
    case ri with
      feq_p _ _ _ _ u => trans join (f a e) ((rev_f A f e) a)
                         trans [u a]
                               join (id_fun A a) a
    end.  


%===== statment that e is an identity w.r.t. (A, f)
%-
<identity_P A f e>
  <and_P <l_identity_P A f e> <r_identity_P A f e> >
-%
Define type_family_abbrev identity_P := 
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A ).<and_P <l_identity_P A f e> <r_identity_P A f e> >.

Define identity_P_l :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( i : <identity_P A f e> ) : <l_identity_P A f e>.
  match i with
    and_p _ _ l _ => cast l by trans cong <l_identity_P * f e> symm inj <identity_P * ** **> i_Eq
                               trans cong <l_identity_P A * e> symm inj <identity_P ** * **> i_Eq
                                     cong <l_identity_P A f *> symm inj <identity_P ** ** *> i_Eq
  end.

Define identity_P_r :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( i : <identity_P A f e> ) : <r_identity_P A f e>.
  match i with
    and_p _ _ _ r => cast r by trans cong <r_identity_P * f e> symm inj <identity_P * ** **> i_Eq
                               trans cong <r_identity_P A * e> symm inj <identity_P ** * **> i_Eq
                                     cong <r_identity_P A f *> symm inj <identity_P ** ** *> i_Eq
  end.


%===== statement that inv is a left inverse map w.r.t. identity e of (A, f)
Inductive l_inv_map_P : Fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A ).type :=
  inv_map_p : Fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
                 ( u : Forall( a : A ).{ (f (inv a) a) = e } ).<l_inv_map_P A f e inv>.

Define l_inv_map_P_total :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( lim : <l_inv_map_P A f e inv> ) : <domain_total_P A A inv>.
  (domain_total_p A A inv
                  foralli( a : A ).
                    case lim with
                      inv_map_p _ _ _ _ u => cinv (inv a) [u a]
                    end ).

Define l_inv_map_P_pf :=
foralli( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
       ( lim : <l_inv_map_P A f e inv> ).     %Forall( a : A ).{ (f (inv a) a) = e }
  foralli( a : A ).
    case lim with
      inv_map_p _ _ _ _ u => trans refl (f (inv a) a)
                             trans [u a]
                                   refl e
    end.


%===== statement that inv is a right inverse map w.r.t. identity e of (A, f)    
%-
<r_inv_map_P A f e inv>.
  <l_inv_map_P A (rev_f A f) e inv>.
-%      
Define type_family_abbrev r_inv_map_P :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A ).<l_inv_map_P A (rev_f A f) e inv>.
              
Define r_inv_map_P_total :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( rim : <r_inv_map_P A f e inv> ) : <domain_total_P A A inv>.
  (l_inv_map_P_total A (rev_f A f) e inv rim).

Define r_inv_map_P_pf :=
foralli( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
       ( rim : <r_inv_map_P A f e inv> ).     %Forall( a : A ).{ (f a (inv a)) = e }
  foralli( a : A ).
    case rim with
      inv_map_p _ _ _ _ u => trans refl (f a (inv a))
                             trans join (f a (inv a)) (rev_f f (inv a) a)
                             trans [u a]
                                   refl e
    end.

                   
%===== statement that inv is a inverse map w.r.t. (A, f)
%-
<inv_map_P A f e inv>
  <and_P <l_inv_map_P A f e inv> <r_inv_map_P A f e inv> >
-%
Define type_family_abbrev inv_map_P := fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A ).
  <and_P <l_inv_map_P A f e inv> <r_inv_map_P A f e inv> >.


Define inv_map_P_l :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( i : <inv_map_P A f e inv> ) : <l_inv_map_P A f e inv>.
  match i with
    and_p _ _ l _ => cast l by trans cong <l_inv_map_P * f e inv> symm inj <inv_map_P * ** ** **> i_Eq
                               trans cong <l_inv_map_P A * e inv> symm inj <inv_map_P ** * ** **> i_Eq
                               trans cong <l_inv_map_P A f * inv> symm inj <inv_map_P ** ** * **> i_Eq
                                     cong <l_inv_map_P A f e *> symm inj <inv_map_P ** ** ** *> i_Eq
  end.

Define inv_map_P_r :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( i : <inv_map_P A f e inv> ) : <r_inv_map_P A f e inv>.
  match i with
    and_p _ _ _ r => cast r by trans cong <r_inv_map_P * f e inv> symm inj <inv_map_P * ** ** **> i_Eq
                               trans cong <r_inv_map_P A * e inv> symm inj <inv_map_P ** * ** **> i_Eq
                               trans cong <r_inv_map_P A f * inv> symm inj <inv_map_P ** ** * **> i_Eq
                                     cong <r_inv_map_P A f e *> symm inj <inv_map_P ** ** ** *> i_Eq
  end.



%===== statement (A, f) forms a group with identity e and inverse mapping inv
Inductive group_def_P : Fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A ). type :=
  group_def_p : Fun( A : type )
                   ( f : Fun( a1 a2 : A ).A )( fa : <bf_assoc_P A f> )
                   ( e : A )( eid : <identity_P A f e> )
                   ( inv : Fun( a : A ). A )( invm : <inv_map_P A f e inv> ). < group_def_P A f e inv >.

Define group_def_P_assoc_pf :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( gr : <group_def_P A f e inv> ) : <bf_assoc_P A f >.
  match gr with
    group_def_p _ _ fa _ _ _ _ => cast fa by trans cong <bf_assoc_P * f> symm inj <group_def_P * ** ** **> gr_Eq
                                                   cong <bf_assoc_P A *> symm inj <group_def_P ** * ** **> gr_Eq
  end.

Define group_def_P_id_pf :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( gr : <group_def_P A f e inv> ) : <identity_P A f e>.
  match gr with
    group_def_p _ _ _ _ eid _ _ => cast eid by trans cong <identity_P * f e> symm inj <group_def_P * ** ** **> gr_Eq
                                               trans cong <identity_P A * e> symm inj <group_def_P ** * ** **> gr_Eq
                                                     cong <identity_P A f *> symm inj <group_def_P ** ** * **> gr_Eq
  end.

Define group_def_P_inv_pf :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A )
   ( gr : <group_def_P A f e inv> ) : <inv_map_P A f e inv>.
  match gr with
    group_def_p _ _ _ _ _ _ invm => cast invm by trans cong <inv_map_P * f e inv> symm inj <group_def_P * ** ** **> gr_Eq
                                                 trans cong <inv_map_P A * e inv> symm inj <group_def_P ** * ** **> gr_Eq
                                                 trans cong <inv_map_P A f * inv> symm inj <group_def_P ** ** * **> gr_Eq
                                                       cong <inv_map_P A f e *> symm inj <group_def_P ** ** ** *> gr_Eq
  end.
  

%===== statement (A, f) forms a group
Inductive group_P : Fun( A : type )( f : Fun( a1 a2 : A ).A ). type :=
  group_p : Fun( A : type )( f : Fun( a1 a2 : A ).A )
               ( e : A )( inv : Fun( a : A ). A )
               ( u : <group_def_P A f e inv> ). < group_P A f >.

Define group_P_id :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( gr : <group_P A f> ) : A.
  match gr with
    group_p _ _ e _ _ => cast e by symm inj <group_P * **> gr_Eq
  end.

Define group_P_inv_map :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( gr : <group_P A f> )( a : A ) : A.
  match gr with
    group_p _ _ _ inv _ => cast (inv a) by symm inj <group_P * **> gr_Eq
  end.
  
%-
Define group_P_pf :=
fun( A : type )( f : Fun( a1 a2 : A ).A )( gr : <group_P A f> ) : <group_def_P A f (group_P_id A f gr) (group_P_inv_map A f gr)>.
  
-%


%====== statement (A, f) with id e and inverse map inv forms an abelian group
Define type_family_abbrev abelian_group_def_P := 
fun( A : type )( f : Fun( a1 a2 : A ).A )( e : A )( inv : Fun( a : A ). A ). 
  < and_P <group_def_P A f e inv> <bf_comm_P A f> >.

%====== statement (A, f) forms an abelian group
Define type_family_abbrev abelian_group_P := 
fun( A : type )( f : Fun( a1 a2 : A ).A ). 
< and_P <group_P A f> <bf_comm_P A f> >.

