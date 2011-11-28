Include "../../guru-lang/lib/bool.g".
Include "../../guru-lang/lib/pair.g".

%===== identity function on A
Define id_fun := fun( A : type )( a : A ) : A. a.
%===== null function from A to B
Define null_fun := fun( A B : type )( a : A ). abort B.

%===== binary identity function from AxB to A, B
Define bin_id_fun1 := fun( A B : type )( a : A )( b : B ) : A. a.
Define const_fun := fun( A B : type )( b : B ).(bin_id_fun1 B A b).
Define const_f := fun( A : type )( a : A ).(const_fun A A a).
Define bin_id_fun2 := fun( A B : type )( a : A )( b : B ) : B. b.
%===== null function on AxB to C
Define bin_null_fun := fun( A B C : type )( a : A ). abort C.


%===== unary to binary conversion
Define utb_fun1 := fun( A B C : type )( f : Fun( b : B ).C )( a : A )( b : B ) : C. (f b).
Define utb_f1 := fun( A : type ).(utb_fun1 A A A).
Define utb_fun2 := fun( A B C : type )( f : Fun( a : A ).B )( a : A )( b : B ) : B. (f a).
Define utb_f2 := fun( A : type ).(utb_fun2 A A A).

%===== binary to unary conversion
Define btu_fun := fun( A B C : type )( f : Fun( a : A )( b : B ).C )( p : <pair A B> ) : C. (f (fst A B p) (snd A B p)).
Define btu_f := fun( A : type ).(btu_fun A A A).



%======= reverse f (take b before a)
Define rev_fun := fun( A B C : type )( f : Fun( a : A )( b : B ).C )( b : B )( a : A ) : C. (f a b).
Define rev_f := fun( A : type ).(rev_fun A A A).


%==== the compose function
Define compose : Fun( A B C : type )( f : Fun( a : A ).B )( g : Fun( b : B ). C )( a : A ). C :=
fun( A B C : type )( f : Fun( a : A ).B )( g : Fun( b : B ). C )( a : A ) : C.
  (g (f a)).

%==== stores a composition from A to B to C
Inductive composition : Fun( A B C : type ). type :=
  mk_composition : Fun( A B C : type )( f : Fun( a : A ).B )( g : Fun( b : B ). C ).< composition A B C >.
  
%======= the while function
Define while_fun : Fun( A : type )( f : Fun( a : A ).bool )( g : Fun( a : A ).A )( a : A ). A :=
fun while_fun( A : type )( f : Fun( a : A ).bool )( g : Fun( a : A ).A )( a : A ) : A.
  match (f a) with
    ff => (while_fun A f g (g a))
  | tt => a
  end.

%======= a function with a domain of A
Inductive fun_domain : Fun( A : type ).type :=
  mk_fun_domain : Fun( A B : type )( f : Fun( a : A ).B ).<fun_domain A>.
  
%======= a function with a range of A
Inductive fun_range : Fun( A : type ).type :=
  mk_fun_range : Fun( A B : type )( f : Fun( b : B ).A ).<fun_range A>.