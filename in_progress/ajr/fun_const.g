Include "equality.g".
Include "fun_defs.g".

%========= statement f is constant
Inductive fun_const_P : Fun( A B : type )( f : Fun( a : A ).B ).type :=
  fun_const_p : Fun( A B : type )( f : Fun( a : A ).B )( b : B )
                   ( u : <feq_P A B f (const_fun A B b)> ).<fun_const_P A B f>.
                  
Define fun_const_P_data :=
fun( A B : type )( f : Fun( a : A ).B )( c : <fun_const_P A B f> ) : B.
  match c with
    fun_const_p _ _ _ b _ => cast b by symm inj <fun_const_P ** * **> c_Eq
  end.
  
  
%========= constant function from A to B
Inductive fun_const : Fun( A B : type ).type :=
  mk_fun_const : Fun( A B : type )( f : Fun( a : A ).B )
                    ( u : <fun_const_P A B f> ).<fun_const A B>.
