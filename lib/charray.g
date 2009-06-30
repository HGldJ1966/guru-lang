%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% char-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "char.g".
Include trusted "unique.g".

%Set "print_parsed".

Define primitive type_family_abbrev charray := fun(A:type).<vec A num_chars> <<END
#define gdelete_charray(x)
END.

Define primitive charray_new : Fun(spec A:type)(^#owned a:A).#unique <charray A> := 
  fun(A:type)(a:A). (mkvec A a num_chars) <<END
void *gcharray_new(void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*128);
  // fprintf(stdout,"gmk_charray(%x).\n", h);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = ginc(a); 
  return h;
}
END.

Define primitive charray_get : Fun(spec A:type)(!#unique l:<charray A>)(#untracked c:char). #<owned l> A := 
  fun(A:type)(l:<charray A>)(c:char). 
    (vec_get A num_chars l (which_char c) [chars_bounded c]) <<END
void *gcharray_get(void *l, int c) {
  return ((void **)l)[c];
}
END.

Define primitive charray_mod 
  : Fun(A:type)(#untracked c:char)(a:A)(#unique l:<charray A>). #unique <charray A> :=
  fun(A:type)(c:char)(a:A)(l:<charray A>).
   (vec_update A num_chars l (which_char c) a [chars_bounded c]) <<END
void *gcharray_mod(int A, int c, void *d, void *l) {
  gdec(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive charray_free : Fun(A:type)(^ #unique l:<charray A>).void :=
  fun(A:type)(l:<charray A>).voidi <<END
void gcharray_free(int A, void *l) {
  int c;
  // fprintf(stdout,"gcvfree(%x).\n", l);
  for (c = 0; c <= 127; c++) 
    gdec(A,((void **)l)[c]);
  carraway_free(l);
}
END.
