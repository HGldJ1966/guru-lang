Include "subset.g".

%========== statement a is in the null subset of A
%-
<null_subset_def_P A f a> 
  <range_P A A (null_fun A A) a>
    <subset_def_P A (null_fun A A) a>
-%
Define type_family_abbrev null_subset_def_P := fun( A : type )( a : A ). <range_P A A (null_fun A A) a>.


%========== the null subset of A
%-
<null_subset_def A f>
  <range A (null_fun A A)>
    <subset_def A (null_fun A A)>
-%
Define type_family_abbrev null_subset_def := fun( A : type ). <range A A (null_fun A A)>.


%========== statment a is in the trivial subset of A
%-
<total_subset_def_P A f a>
  <range_P A A (id_fun A) a>
    <subset_def_P A (id_fun A) a>
-%
Define type_family_abbrev trivial_subset_def_P := fun( A : type )( a : A ). <range_P A A (id_fun A) a>.
%========== the trivial subset of A
%-
<total_subset_def A f>
  <range A A (id_fun A) a>
    <subset_def A (id_fun A)>
-%
Define type_family_abbrev trivial_subset_def := fun( A : type ). <range_P A A (id_fun A)>.



%========= proper subset of A?
%========= non-empty subset of A?
