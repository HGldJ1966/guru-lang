%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% char-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "char.g".
Include trusted "unique.g".

%Set "print_parsed".

Define primitive type_family_abbrev charvec := fun(A:type).<vec A num_chars> <<END
#define gdelete_charvec(x) carraway_free(x)
END.

Define primitive mk_charvec : Fun(spec A:type)(^#owned a:A).#unique <charvec A> := 
  fun(A:type)(a:A). (mkvec A a num_chars) <<END
void *gmk_charvec(void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*128);
  // fprintf(stdout,"gmk_charvec(%x).\n", h);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = ginc(a); 
  return h;
}
END.

Define primitive cvget : Fun(spec A:type)(!#unique l:<charvec A>)(#untracked c:char). #<owned l> A := 
  fun(A:type)(l:<charvec A>)(c:char). 
    (vec_get A num_chars l (which_char c) [chars_bounded c]) <<END
void *gcvget(void *l, int c) {
  return ((void **)l)[c];
}
END.

Define primitive cvupdate 
  : Fun(A:type)(#untracked c:char)(a:A)(#unique l:<charvec A>). #unique <charvec A> :=
  fun(A:type)(c:char)(a:A)(l:<charvec A>).
   (vec_update A num_chars l (which_char c) a [chars_bounded c]) <<END
void *gcvupdate(int A, int c, void *d, void *l) {
  gdec(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive cvfree : Fun(A:type)(^ #unique l:<charvec A>).void :=
  fun(A:type)(l:<charvec A>).voidi <<END
void gcvfree(int A, void *l) {
  int c;
  // fprintf(stdout,"gcvfree(%x).\n", l);
  for (c = 0; c <= 127; c++) 
    gdec(A,((void **)l)[c]);
  carraway_free(l);
}
END.
