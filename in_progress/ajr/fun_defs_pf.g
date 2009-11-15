Include "fun_defs.g".
Include "../../guru-lang/lib/nat.g".
Include "domain.g".
Include "range.g".
Include "equality.g".

%===== identity is total
Define id_fun_total := 
fun( A : type ) : < domain_total_P A A (id_fun A) >.
  (domain_total_p A A (id_fun A)
                  foralli( a : A ).
                    existsi a { (id_fun A a) = * }
                      join (id_fun A a) a ).
                      
%===== identity is surjective
Define id_fun_range_total := 
fun( A : type ) : < range_total_P A A (id_fun A) >.
  (range_total_p A A (id_fun A)
                 foralli( a : A ).
                   existsi a { (id_fun A *) = a }
                     join (id_fun A a) a ).                 


%===== binary identity function from AxB to A, B
Define bin_id_fun2_feq_P :=
fun( A B : type )( a : A ) : <feq_P B B (id_fun B) (bin_id_fun2 A B a)>.
  (feq_p B B (id_fun B) (bin_id_fun2 A B a)
         foralli( b : B ).
           trans join (id_fun B b) b
                 join b (bin_id_fun2 A B a b)).
                 
%-              
Define bin_id_fun_rev_feq_P :=
fun( A B : type )( a : A ) : <feq_P A B (bin_id_fun1 A B a) (bin_id_fun2 A B a)>.
  (feq_p B B (id_fun B) (bin_id_fun2 A B a)
         foralli( b : B ).
           trans join (id_fun B b) b
                 join b (bin_id_fun2 A B a b)).              
-%

%===== binary identity function from AxB to A, B
Define bin_id_fun1_total := 
foralli( A B : type )( a : A )( b : B ). 
  existsi a { (bin_id_fun1 A B a b) = * }
    join (bin_id_fun1 A B a b) a.
Total bin_id_fun1 bin_id_fun1_total.

Define const_fun_total := 
foralli( A B : type )( b : B )( a : A ). 
  existsi (bin_id_fun1 A B a b) { (const_fun A B a b) = * }
    join (const_fun A B a b) (bin_id_fun1 A B a b).
Total const_fun const_fun_total.
    
Define const_f_total := 
foralli( A : type )( a a' : A ).
  existsi (const_fun A A a a') { (const_f A a a') = * }
    join (const_f A a a') (const_fun A A a a').
Total const_f const_f_total.
    
Define bin_id_fun2_total := 
foralli( A B : type )( a : A )( b : B ). 
  existsi b { (bin_id_fun2 A B a b) = * }
    join (bin_id_fun2 A B a b) b.
Total bin_id_fun2 bin_id_fun2_total.



%Define btu_total :=


Define btu_pf :=
foralli( A B C : type )( f : Fun( a : A )( b : B ).C )( a : A )( b : B ).     %(btu_fun A B C f (mkpair A B a b)) = (f a b)
  join (btu_fun A B C f (mkpair A B a b)) (f a b).














%-
%==== statement:  i is an inductive argument on function f
Inductive ind_arg_P : Fun( A : type )( f : Fun( a : A ).A )( i : Fun( a : A ).nat ). type :=
  ind_arg_p : Fun( A : type )( f : Fun( a : A ).A )( i : Fun( a : A ).nat )
                 ( u : Forall( a : A )( n : nat )( u' : { (lt (i a) (S n)) = tt } ). { (lt (i (f a)) n) = tt } ).< ind_arg_P A f i>.


Define ind_arg_P_pf : Forall( A : type )( f : Fun( a : A ).A )( i : Fun( a : A ).nat )
                            ( ia : <ind_arg_P A f i> )( a : A )( n : nat )( u' : { (lt (i a) (S n)) = tt } ). 
                        { (lt (i (f a)) n) = tt } :=
foralli( A : type )( f : Fun( a : A ).A )( i : Fun( a : A ).nat )( ia : <ind_arg_P A f i> )( a : A )( n : nat )
       ( u' : { (lt (i a) (S n)) = tt } ).
  case ia with
    ind_arg_p _ _ _ u => 
      trans refl (lt (i (f a)) n)
            [u a n u']
  end.
  
  
%-
Define ind_arg_run  :=   
fun ind_arg_run( A : type )
               ( f : Fun( a : A ).A )( f_t : <domain_total_P A bool f> )
               ( i : Fun( a : A ).nat )( i_t : <domain_total_P A nat i> )
               ( ia : <ind_arg_P A f i> )( ibn : nat )
               ( P : type )( p : <or_P P _ > ) : <domain_total Unit P>.
  match ibn with
    Z => %contradiction
  | S ibn' =>
     match p with
       or_p1 _ _ p' => %base case
     | or_p2 _ _ p' => %call to IH
     end
  end.
-%

%==== an inductive argument on function f
Inductive ind_arg : Fun( A : type )( f : Fun( a : A ).A ).type :=
  mk_ind_arg : Fun( A : type )( f : Fun( a : A ).A )( i : Fun( a : A ).nat )
                  ( u : <ind_arg_P A f i> ).< ind_arg A f >.


%-
Define while_fun_total : Forall( A : type )
                            ( f : Fun( a : A ).bool )( f_t : <domain_total_P A bool f> )
                            ( g : Fun( a : A ).A )( g_t : <domain_total_P A A g> ).
                        <domain_total_P A A (while_fun A f g a)>
-%

Define while_fun_pf : Forall( A : type )
                            ( f : Fun( a : A ).bool )( f_t : <domain_total_P A bool f> )
                            ( g : Fun( a : A ).A )( g_t : <domain_total_P A A g> )
                            ( ifn : Fun( a : A ).nat )( ifn_t : <domain_total_P A nat ifn> )
                            ( ia : <ind_arg_P A g ifn> )( a : A ). 
                        { (f (while_fun A f g a)) = tt } :=
foralli( A : type )
       ( f : Fun( a : A ).bool )( f_t : <domain_total_P A bool f> )
       ( g : Fun( a : A ).A )( g_t : <domain_total_P A A g> )
       ( ifn : Fun( a : A ).nat )( ifn_t : <domain_total_P A nat ifn> )
       ( ia : <ind_arg_P A g ifn> )( a : A ).
  abbrev ifnt = terminates (ifn a) by [domain_total_P_pf A nat ifn ifn_t a] in
  [ 
  induction ( ibn : nat ) by uibn uIbn IHibn return Forall( a' : A )( u : { (lt (ifn a') ibn) = tt } ).
                                                      { (f (while_fun A f g a')) = tt } with
    Z => 
      foralli( a' : A )( u : { (lt (ifn a') ibn) = tt } ).
        abbrev ifnt' = terminates (ifn a') by [domain_total_P_pf A nat ifn ifn_t a'] in
        contra
          trans trans symm u 
                trans cong (lt ifnt' *) uibn
                      [lt_Z ifnt']
                clash ff tt
          { (f (while_fun A f g a')) = tt }
  | S ibn' =>
     foralli( a' : A )( u : { (lt (ifn a') ibn) = tt } ).
        abbrev ft = terminates (f a') by [domain_total_P_pf A bool f f_t a'] in
        abbrev gt = terminates (g a') by [domain_total_P_pf A A g g_t a'] in
        case ft by ut uT with
          ff => 
              trans cong (f *) hypjoin (while_fun A f g a') (while_fun A f g gt) by ut end
                    [IHibn ibn' gt [ind_arg_P_pf A g ifn ia a' ibn' trans cong (lt (ifn a') *) symm uibn 
                                                                          u]]
        | tt =>
              trans cong (f *) hypjoin (while_fun A f g a') a' by ut end
                    ut
        end
  end
  (S ifnt) a [lt_S ifnt] ].
-%
  
Define rev_fun_pf :=
foralli( A B C : type )( f : Fun( a : A )( b : B ).C )( b : B )( a : A ).     % { ((rev_fun A B C f) b a) = (f a b) }
  join ((rev_fun A B C f) b a) (f a b).


