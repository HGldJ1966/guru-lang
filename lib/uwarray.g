%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of untracked data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique_owned.g".
Include trusted "comparator.g".

%Set "print_parsed".

Define primitive type_family_abbrev uwarray := fun(A:type)(n:word).<vec A (word_to_nat n)> <<END
#define gdelete_uwarray(x)
END.

Define primitive uwarray_new
 : Fun(spec A:type)(n:word)(#untracked a:A).#unique <uwarray A n> := 
  fun(spec A:type)(n:word)(a:A). (mkvec A a (word_to_nat n)) <<END
void *guwarray_new(unsigned int n, int a) {
  void **h = (void **)guru_malloc(sizeof(int)*n);
  // fprintf(stdout,"gmk_uwarray(%x).\n", h);
  unsigned int c;
  for (c = 0; c < n; c++)
    h[c] = a; 
  return h;
}
END.

Define primitive uwarray_get
   : Fun(A:type)(spec n:word)(! #unique_owned l:<uwarray A n>)
        (i:word)(u:{(ltword i n) = tt}). #untracked A := 
  fun(A:type)(spec n:word)(l:<uwarray A n>)(i:word)(u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
    (vec_get A (word_to_nat n) l (word_to_nat i) p) <<END
inline void* guwarray_get(void **l, unsigned int i) { return l[i]; }
END.

Define primitive uwarray_set 
  : Fun(A:type)(spec n:word)(#unique l:<uwarray A n>)
       (i:word)(#untracked a:A)
       (u:{(ltword i n) = tt}). #unique <uwarray A n> :=
  fun(A:type)(spec n:word)(l:<uwarray A n>)
     (i:word)(a:A)
     (u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
   (vec_update A (word_to_nat n) l (word_to_nat i) a p) <<END
void *guwarray_set(int A, void *l, unsigned int c, void *d) {
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive uwarray_free : Fun(A:type)(spec n:word)(^ #unique l:<uwarray A n>).void :=
  fun(A:type)(spec n:word)(l:<uwarray A n>).voidi <<END
void guwarray_free(int A, void *l) {
  // fprintf(stdout,"guwarray_free(%x).\n", l);
  carraway_free(l);
}
END.

