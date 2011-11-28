Include "domain.g".
Include "range.g".

%==== logic true and false
Inductive true_P : type :=
  true_p : true_P.
Inductive false_P : type :=
  false_p : Fun( A : type )( a : A )( u : { a != a } ). false_P.


%==== the statement A and B is true
Inductive and_P : Fun( A B : type ).type :=
  and_p : Fun( A B : type )( a : A )( b : B ).< and_P A B >.
  
Define and_P1 :=
fun( A B : type )( s : <and_P A B > ) : A.
  match s with
    and_p _ _ a _ => cast a by symm inj <and_P * **> s_Eq
  end.
  
Define and_P2 :=
fun( A B : type )( s : <and_P A B > ) : B.
  match s with
    and_p _ _ _ b => cast b by symm inj <and_P ** *> s_Eq
  end.
  


%==== the statement A or B is true
Inductive or_P : Fun( A B : type ).type :=
  or_p1 : Fun( A B : type )( a : A ). < or_P A B >
| or_p2 : Fun( A B : type )( b : B ). < or_P A B >.




%==== the statement A -> B is true
Define type_family_abbrev implies_P := fun( A B : type ). < domain_total A B >.





%==== the statement A is not true
Define type_family_abbrev not_P := fun( A : type ). <implies_P A false_P>.




%==== the statement Forall( a : A ). ( f a ) is true
%Define type_family_abbrev forall_P := fun( A B C : type )( a : A )( f : Fun( a : A )( b : B ).C ). < domain_total_P B C (f a) >.




%==== the statement Exists( a : A ). f is true
%Define type_family_abbrev exists_P :=        ????
%fun( A B : type )( f : fun( a : A ).B ). < range A B f >.





%==== A is unique
%-
Define type_family_abbrev unique_P := fun( A : type ).<inj_map A Unit>.
-%

