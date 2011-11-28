Include "../../guru-lang/lib/bool.g".
Include "subset.g".

Define selector : Fun( A : type )( f : Fun( a : A ).bool )( a : A ). A :=
fun( A : type )( f : Fun( a : A ).bool )( a : A ).
  match (f a) with
    ff => abort A
  | tt => a
  end.  
  
  
%========== statement a is in the subset of A defined by the range of (selector A f)
%-
<sel_subset_def_P A f a>
  <range_P A A (selector A f) a>
    <subset_def_P A (selector A f) a>
-%
Define type_family_abbrev sel_subset_def_P := fun( A : type )( f : Fun( a : A ).bool )( a : A ). < range_P A A (selector A f) a>. 

%========== the subset of A defined by the range of (selector A f)
%-
<sel_subset_def A f>
  <range A A (selector A f) a>
    <subset_def A (selector A f)>
-%
Define type_family_abbrev sel_subset_def := fun( A : type )( f : Fun( a : A ).bool ). <range A A (selector A f)>. 