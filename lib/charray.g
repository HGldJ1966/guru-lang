%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% char-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include "char.g".
Include "warray.g".

%Set "print_parsed".

%Set "debug_check_spec".

Define type_family_abbrev charray := fun(A:type).<warray A num_chars_word>.

Define charray_new : Fun(spec A:type)(^#owned a:A).#unique <charray A> := 
 fun(spec A:type)(^#owned a:A):#unique <charray A>.
  (warray_new A num_chars_word a).

Define charray_get : Fun(spec A:type)(!#unique l:<charray A>)(#untracked c:char). #<owned l> A := 
  fun(spec A:type)(!#unique l:<charray A>)(#untracked c:char):#<owned l> A. 
    (warray_get A num_chars_word l (c2w c) [chars_bounded4 c]).

Define charray_set 
  : Fun(A:type)(#untracked c:char)(a:A)(#unique l:<charray A>). #unique <charray A> :=
  fun(A:type)(#untracked c:char)(a:A)(#unique l:<charray A>):#unique <charray A>.
   (warray_set A (c2w c) a num_chars_word l [chars_bounded4 c]).

Define charray_free : Fun(A:type)(^ #unique l:<charray A>).void :=
  fun(A:type)(^ #unique l:<charray A>).
    (warray_free A num_chars_word l).
