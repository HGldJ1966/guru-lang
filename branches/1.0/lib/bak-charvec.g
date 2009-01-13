Include "char.g".
Include "list.g".
Include "unit.g".

Define mk_charvec := 
  fun (A:type)(a:A):unique <vec A num_chars>.
    (mkvec A a num_chars).

Define cvget := 
  fun(A:type)(unique_owned l:<vec A num_chars>)(c:char) : A. 
    (vec_get A num_chars l (which_char c) [chars_bounded c]).

Define cvupdate := 
  fun(A:type)(unique l:<vec A num_chars>)(c:char)(a:A)
   : unique <vec A num_chars>.
   (vec_update A num_chars l (which_char c) a [chars_bounded c]).

Define mk_ucharvec := 
  fun (A:type)(f:Fun(u:Unit).unique A):unique <vec A num_chars>.
    (mkvec A (f unit) num_chars).

Define ucvget :=
  fun(A:type)(unique_owned l:<vec A num_chars>)(c:char)(B C : type)
     (b:B)(f:Fun(b:B)(unique_owned a:A).C) : C. 
    (f b (vec_get A num_chars l (which_char c) [chars_bounded c])).

Define ucvupdate := 
  fun(A:type)(unique l:<vec A num_chars>)(c:char)(unique a:A)
   : unique <vec A num_chars>.
   (vec_update A num_chars l (which_char c) a [chars_bounded c]).

Define ucvmod :=
  fun(A:type)(unique l:<vec A num_chars>)(c:char)(B:type)
     (b:B)(f:Fun(b:B)(unique a:A).unique A) : unique <vec A num_chars>. 
    (ucvupdate A l c
       (f b (vec_get A num_chars l (which_char c) [chars_bounded c]))).

