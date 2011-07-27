%=============================================================================
% word-indexed arrays of unique data
%=============================================================================

Include trusted "word.g".
Include trusted "unique_owned.g".

%Set "print_parsed".

Define primitive type_family_abbrev qwarray := fun(A:type)(n:word).<vec A (word_to_nat n)> <<END
#define gdelete_qwarray(x)
END.

Define primitive qwarray_new
 : Fun(spec A:type)(n:word)(f:Fun(i:word).A).#unique <qwarray A n> := 
  fun(spec A:type)(n:word)(f:Fun(i:word).A). (mkvec A (f word0) (word_to_nat n)) <<END
void *gqwarray_new(int n, void* (*f)(int), void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*n);
  int c;
  for (c = 0; c < n; c++)
    h[c] = f(c); // f is a generator function.
  return h;
}
END.

Define primitive qwarray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<qwarray A n>)
        (i:word)
        (u:{(ltword i n) = tt}). #<unique_owned l> A := 
  fun(A:type)(spec n:word)(l:<qwarray A n>)(i:word)(u:{(ltword i n) = tt}). 
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
  (vec_get A (to_nat wordlen n) l (to_nat wordlen i) p) <<END
inline void* gqwarray_get(void **l, int i) { return l[i]; }
END.

Define primitive qwarray_set 
  : Fun(A:type)(i:word)(#unique a:A)(spec n:word)(#unique l:<qwarray A n>)
       (u:{(ltword i n) = tt}). #unique <qwarray A n> :=
  fun(A:type)(i:word)(a:A)(spec n:word)(l:<qwarray A n>)(u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a p) <<END
void *gqwarray_set(int A, int c, void *d, void *l) {
  gconsume_unique(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive qwarray_free : Fun(A:type)(n:word)(^ #unique l:<qwarray A n>).void :=
  fun(A:type)(n:word)(l:<qwarray A n>).voidi <<END
void gwarray_free(int A, int n, void *l) {
  int c;
  // fprintf(stdout,"gwarray_free(%x).\n", l);
  for (c = 0; c < n; c++) 
    gconsume_unique(A,((void **)l)[c]);
  carraway_free(l);
}
END.
