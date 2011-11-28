%=============================================================================
% word-indexed arrays of unique data
%=============================================================================
Include trusted "unit.g".
Include trusted "word.g".
Include trusted "unique_owned.g".

%Set "print_parsed".

Define primitive type_family_abbrev qwarray := fun(A:type)(n:word).<vec A (word_to_nat n)> <<END
#define gdelete_qwarray(x)
END.

Define primitive qwarray_new
 : Fun(spec A:type)(n:word)(f:Fun(u:Unit).#unique A).#unique <qwarray A n> := 
  fun(A:type)(n:word)(f:Fun(u:Unit).A). (mkvec A (f unit) (word_to_nat n)) <<END
void *gqwarray_new(unsigned n, void* (*f)(void*)) {
  void **h = (void **)guru_malloc(sizeof(void *)*n);
  unsigned c;
  for (c = 0; c < n; c++)
    h[c] = f(gunit()); // f is a generator function.
  return h;
}
END.

Define primitive qwarray_free : Fun(A:type)(n:word)(^ #unique l:<qwarray A n>).void :=
  fun(A:type)(n:word)(l:<qwarray A n>).voidi <<END
void gqwarray_free(int A, unsigned n, void *l) {
  unsigned c;
  // fprintf(stdout,"gwarray_free(%x).\n", l);
  for (c = 0; c < n; c++) 
    gconsume_unique(A,((void **)l)[c]);
  carraway_free(l);
}
END.

% read-only access
Define primitive qwarray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<qwarray A n>)
        (i:word)
        (u:{(ltword i n) = tt}). #<unique_owned l> A := 
  fun(A:type)(spec n:word)(l:<qwarray A n>)(i:word)(u:{(ltword i n) = tt}). 
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
  (vec_get A (to_nat wordlen n) l (to_nat wordlen i) p) <<END
inline void* gqwarray_get(void **l, int i) { return l[i]; }
END.

% replace an item
Define primitive qwarray_set 
  : Fun(A:type)(spec n:word)(#unique l:<qwarray A n>)
  		 (i:word)(#unique a:A)(u:{(ltword i n) = tt}). #unique <qwarray A n> :=
  fun(A:type)(spec n:word)(l:<qwarray A n>)(i:word)(a:A)(u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a p) <<END
void *gqwarray_set(int A, void *l, unsigned c, void *d) {
  gconsume_unique(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

% take out and replace an item
Inductive qwarray_swap_t : Fun(A:type)(n:word).type :=
  qwarray_swap_v : Fun(A:type)(#unique a:A)
  										(spec n:word)(#unique l:<qwarray A n>)
                      .#unique <qwarray_swap_t A n>.

Define primitive qwarray_swap : Fun
  (A:type)(spec n:word)(#unique l:<qwarray A n>)
  (i:word)(#unique a:A)
  (u:{(ltword i n) = tt}). #unique <qwarray_swap_t A n> :=
  fun(A:type)(spec n:word)(l:<qwarray A n>)(i:word)(a:A)(u:{(ltword i n) = tt})
  .
  cabbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
  cabbrev a' = (vec_get A (to_nat wordlen n) l (to_nat wordlen i) p)
  cabbrev l' = (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a p)
  (qwarray_swap_v A a' n l')
  <<END
void *gqwarray_swap(int A, void *l, unsigned c, void *d) {
  void*	tmp = ((void **)l)[c];
  ((void **)l)[c] = d;
  return gqwarray_swap_v(A,tmp,l);
}
END.
