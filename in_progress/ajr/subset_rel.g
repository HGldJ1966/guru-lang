Include "subset_pf.g".
Include "logic_defs.g".

%==== statement that a is in the union of subsets A|f1 and A|f2
Define type_family_abbrev set_union_P :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( a : A ).<or_P <subset_def_P A f1 a> <subset_def_P A f2 a> >. 

%===== union of subsets A|f1 and A|f2
Inductive set_union : Fun( A : type )( f1 f2 : Fun( a : A ).A ). type :=
  mk_set_union1 : Fun( A : type )( f1 f2 : Fun( a : A ).A )( a : A )( u : <subset_def_P A f1 a> ).<set_union A f1 f2>
| mk_set_union2 : Fun( A : type )( f1 f2 : Fun( a : A ).A )( a : A )( u : <subset_def_P A f2 a> ).<set_union A f1 f2>.

Define set_union_data :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( su : <set_union A f1 f2> ) : A.
  match su with
    mk_set_union1 _ _ _ a _ => cast a by symm inj <set_union * ** **> su_Eq
  | mk_set_union2 _ _ _ a _ => cast a by symm inj <set_union * ** **> su_Eq
  end.
  
Define set_union_pf :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( su : <set_union A f1 f2> ) : <set_union_P A f1 f2 (set_union_data A f1 f2 su)>.
  match su with
    mk_set_union1 _ _ _ a u => (or_p1 <subset_def_P A f1 (set_union_data A f1 f2 su)> <subset_def_P A f2 (set_union_data A f1 f2 su)> 
                                     (eq_subset_def_P A f1 a (set_union_data A f1 f2 su)
                                                      hypjoin a (set_union_data A f1 f2 su) by su_eq end u))
  | mk_set_union2 _ _ _ a u => (or_p2 <subset_def_P A f1 (set_union_data A f1 f2 su)> <subset_def_P A f2 (set_union_data A f1 f2 su)> 
                                                    (eq_subset_def_P A f2 a (set_union_data A f1 f2 su)
                                                                     hypjoin a (set_union_data A f1 f2 su) by su_eq end u))
  end.


%===== statement that a is in the intersection of subsets A|f1 and A|f2
Define type_family_abbrev set_intersect_P :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( a : A ).<and_P <subset_def_P A f1 a> <subset_def_P A f2 a> >. 

%====== intersection of subsets A|f1 and A|f2
Inductive set_intersect : Fun( A : type )( f1 f2 : Fun( a : A ).A ). type :=
  mk_set_intersect : Fun( A : type )( f1 f2 : Fun( a : A ).A )( a : A )
                        ( u1 : <subset_def_P A f1 a> )
                        ( u2 : <subset_def_P A f2 a> ).<set_intersect A f1 f2>.

Define set_intersect_data :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( si : <set_intersect A f1 f2> ) : A.
  match si with
    mk_set_intersect _ _ _ a _ _ => cast a by symm inj <set_intersect * ** **> si_Eq
  end.
  
Define set_intersect_pf :=
fun( A : type )( f1 f2 : Fun( a : A ).A )( si : <set_intersect A f1 f2> ) : <set_intersect_P A f1 f2 (set_intersect_data A f1 f2 si)>.
  match si with
    mk_set_intersect _ _ _ a u1 u2 => 
      abbrev deqa = hypjoin a (set_intersect_data A f1 f2 si) by si_eq end in
      (and_p <subset_def_P A f1 (set_intersect_data A f1 f2 si)> <subset_def_P A f2 (set_intersect_data A f1 f2 si)> 
             (eq_subset_def_P A f1 a (set_intersect_data A f1 f2 si) deqa u1)
             (eq_subset_def_P A f2 a (set_intersect_data A f1 f2 si) deqa u2))
  end.
  
  
%===== set null
Define type_family_abbrev set_null_P := not_P.