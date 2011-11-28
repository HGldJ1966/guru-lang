Include "equality.g".


Define feq_refl_P :=
fun( A B : type  )
   ( f : Fun( a : A ).B ) : <feq_P A B f f>.
  (feq_p A B f f
         foralli( a : A ).
           refl (f a) ).


Define feq_symm_P :=
fun( A B : type  )
   ( f : Fun( a : A ).B )
   ( g : Fun( a : A ).B )
   ( e1 : <feq_P A B f g> ) : <feq_P A B g f>.
  (feq_p A B g f
         foralli( a : A ).
           symm [feq_P_pf A B f g e1 a] ).


Define feq_trans_P :=
fun( A B : type  )
   ( f : Fun( a : A ).B )
   ( g : Fun( a : A ).B )
   ( h : Fun( a : A ).B )
   ( e1 : <feq_P A B f g> )
   ( e2 : <feq_P A B g h> ) : <feq_P A B f h>.
  (feq_p A B f h
         foralli( a : A ).
           trans [feq_P_pf A B f g e1 a]
                 [feq_P_pf A B g h e2 a] ).


Define feq_pf :=           
fun( A B : type )( f : Fun( a : A ). B )( fe : <feq A B f> ) : <feq_P A B f (feq_data A B f fe)>.
  match fe with 
    mk_feq _ _ _ g u => 
      (feq_p A B f (feq_data A B f fe)
         foralli( a : A ).
           trans refl (f a)
           trans [feq_P_pf A B f g u a]
                 symm hypjoin ((feq_data A B f fe) a) (g a) by fe_eq end )
  end. 