Include "fiber.g".

%=======  statement that a is equal to b
Inductive eq_P : Fun( A : type )( a1 a2 : A ). type :=
  mk_eq_P : Fun( A : type )( a1 a2 : A )( u : { a1 = a2 } ). <eq_P A a1 a2>.

Define eq_P_pf : Forall( A : type )( a1 a2 : A )( e : <eq_P A a1 a2> ).{ a1 = a2 } :=
foralli( A : type )( a1 a2 : A )( e : <eq_P A a1 a2> ).
  case e with
    mk_eq_P _ _ _ u => trans refl a1
                       trans u
                             refl a2
  end.
  
  
%=======  statement that f is equal to g at a
%-
<feq_at_P A B f g a>
  <fiber B B (const_f B (g a)) (f a)>
    <fiber_P A B f (g a) a>
      <range_P B B (const_f B (g a)) (f a)>
      <subset_def_P B (const_f B (g a)) (f a)>
        <singleton_subset_def_P B (g a) (f a)>    
-%
Define type_family_abbrev feq_at_P :=
fun( A B : type )( f g : Fun( a : A ). B )( a : A ). <fiber B B (const_f B (g a)) (f a)>.

Define feq_at_P_pf :=
foralli( A B : type )( f g : Fun( a : A ). B )( a : A )( fe : <feq_at_P A B f g a> ).
  case fe with
    mk_fiber _ _ _ _ b' u =>
      symm trans join (g a) (const_f B (g a) b')
           trans u
                 refl (f a)
  end.
%[fiber_P_pf A B f (g a) a]   note that this should be legal based on the structure of fiber_P_pf

  
%======= points where f is equal to g
Inductive feq_at : Fun( A B : type )( f g : Fun( a : A ). B ). type :=
  mk_feq_at : Fun( A B : type )( f g : Fun( a : A ). B )( a : A )
                 ( u : <feq_at_P A B f g a> ). <feq_at A B f g>.

Define feq_at_data :=
fun( A B : type )( f g : Fun( a : A ). B )( fea : <feq_at A B f g> ) : A.
  match fea with
    mk_feq_at _ _ _ _ a _ => cast a by symm inj <feq_at * ** ** **> fea_Eq
  end.
 

%=======  predicate that f is equal to g
Define predicate feq_pred := fun( A B : type )( f g : Fun( a : A ). B ). Forall( a : A ).{ (f a) = (g a) }.
%=======  statement that f is equal to g
Inductive feq_P : Fun( A B : type )( f g : Fun( a : A ). B ). type :=
  feq_p : Fun( A B : type )( f g : Fun( a : A ). B )
             ( u : @<feq_pred A B f g> ). <feq_P A B f g>.
                       
Define feq_P_pf :=
foralli( A B : type )( f g : Fun( a : A ). B )( fe : <feq_P A B f g> ). %<feq_p A B f g>
  case fe with
    feq_p _ _ _ _ u => 
      foralli( a : A ).
        trans refl (f a) 
        trans [u a]
              refl (g a)
  end.



%==== functions that are equal to f
Inductive feq : Fun( A B : type )( f : Fun( a : A ). B ). type :=
  mk_feq : Fun( A B : type )( f g : Fun( a : A ). B )( u : <feq_P A B f g> ). <feq A B f>.
  
Define feq_data : Fun( A B : type )( f : Fun( a : A ). B )( fe : <feq A B f> )( a : A ). B :=
fun( A B : type )( f : Fun( a : A ). B )
   ( fe : <feq A B f> )( a : A ) : B.
  match fe with
    mk_feq _ _ _ g _ => cast (g a) by symm inj <feq ** * **> fe_Eq
  end.
                    
                     
                     
                                             
%=======  predicate that f is equal to g     
Define predicate bfeq_pred := fun( A B C : type )( f g : Fun( a : A )( b : B ).C ). Forall( a : A ). @<feq_pred B C (f a) (g a)>.
%=======  statement that f is equal to g
Inductive bfeq_P : Fun( A B C : type )( f g : Fun( a : A )( b : B ).C ). type :=
  bfeq_p : Fun( A B C : type )( f g : Fun( a : A )( b : B ).C )
             ( u : @<bfeq_pred A B C f g> ). <bfeq_P A B C f g>.
                       
Define bfeq_P_pf :=
foralli( A B C : type )( f g : Fun( a : A )( b : B ).C )( bfe : <bfeq_P A B C f g> ). %<bfeq_p A B f g>
  case bfe with
    bfeq_p _ _ _ _ _ u => 
      foralli( a : A )( b : B ).
        trans refl (f a b) 
        trans [u a b]
              refl (g a b)
  end.
  