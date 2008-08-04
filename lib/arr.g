Include "vec.g".

Define mk_arr := 
  fun (A:type)(a:A):unique <vec A num_chars>.
    (mkvec A a num_chars).

Define arr_get := 
  fun(A:type)(unique_owned l:<vec A num_chars>)(c:char) : A. 
    (vec_get A num_chars l (which_char c) [chars_bounded c]).

Define arr_update := 
  fun(A:type)(unique l:<vec A num_chars>)(c:char)(a:A)
   : unique <vec A num_chars>.
   (vec_update A num_chars l (which_char c) a [chars_bounded c]).

