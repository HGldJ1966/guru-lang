%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% char-indexed arrays of untracked data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include "char.g".
Include "uwarray.g".

%Set "print_parsed".

%Set "debug_check_spec".

Define type_family_abbrev ucharray := fun(A:type).<uwarray A num_chars_word>.

Define ucharray_new : Fun(spec A:type)(#untracked a:A).#unique <ucharray A> := 
 fun(spec A:type)(#untracked a:A):#unique <ucharray A>.
  (uwarray_new A num_chars_word a).

Define ucharray_get : Fun(spec A:type)(!#unique l:<ucharray A>)(#untracked c:char). #untracked A := 
  fun(spec A:type)(!#unique l:<ucharray A>)(#untracked c:char):#untracked A. 
    (uwarray_get A num_chars_word l (c2w c) [chars_bounded3 c]).

Define ucharray_set 
  : Fun(A:type)(#untracked c:char)(#untracked a:A)(#unique l:<ucharray A>). #unique <ucharray A> :=
  fun(A:type)(#untracked c:char)(a:A)(#unique l:<ucharray A>):#unique <ucharray A>.
   (uwarray_set A (c2w c) a num_chars_word l [chars_bounded3 c]).

Define ucharray_free : Fun(A:type)(^ #unique l:<ucharray A>).void :=
  fun(A:type)(^ #unique l:<ucharray A>).
    (uwarray_free A num_chars_word l).
