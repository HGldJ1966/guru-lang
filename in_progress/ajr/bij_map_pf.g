Include "bij_map.g".
                 
%======== if f = g and f is a bijection, then g is a bijection
Define func_equality_bij_map_P :=
fun( A B : type )( f : Fun( a : A ).B )( g : Fun( a : A ).B )( fe : <func_equality_P A B f g> )
   ( b : <bij_map_P A B f> ) : <bij_map_P A B g>.
   (bij_map_p A B g
              (func_equality_inj_map_P A B f g fe (bij_map_P_inj A B f b))
              (func_equality_range_total_P A B f g fe (bij_map_P_surj A B f b))).
              
              
              
              
              