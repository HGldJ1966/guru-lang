%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of untracked data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique_owned.g".
Include trusted "comparator.g".

%Set "print_parsed".

Define primitive type_family_abbrev uwarray := fun(A:type)(n:nat).<vec A n> <<END
#define gdelete_uwarray(x)
END.

Define primitive uwarray_new
 : Fun(spec A:type)(n:word)(#untracked a:A).#unique <uwarray A (word_to_nat n)> := 
  fun(A:type)(n:word)(a:A). (mkvec A a (to_nat wordlen n)) <<END
void *guwarray_new(int n, int a) {
  void **h = (void **)guru_malloc(sizeof(int)*n);
  // fprintf(stdout,"gmk_uwarray(%x).\n", h);
  int c;
  for (c = 0; c < n; c++)
    h[c] = a; 
  return h;
}
END.

Define primitive uwarray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<uwarray A (word_to_nat n)>)
        (i:word)
        (u:{(lt (to_nat i) (to_nat n)) = tt}). #untracked A := 
  fun(A:type)(spec n:word)(l:<uwarray A (word_to_nat n)>)(i:word)(u:{(lt (to_nat i) (to_nat n)) = tt}). 
    (vec_get A (to_nat wordlen n) l (to_nat wordlen i) u) <<END
inline void* guwarray_get(void **l, int i) { return l[i]; }
END.

Define primitive uwarray_set 
  : Fun(A:type)(i:word)(#untracked a:A)(spec n:word)(#unique l:<uwarray A (word_to_nat n)>)
       (u:{(lt (to_nat i) (to_nat n)) = tt}). #unique <uwarray A (word_to_nat n)> :=
  fun(A:type)(i:word)(a:A)(spec n:word)(l:<uwarray A (word_to_nat n)>)(u:{(lt (to_nat i) (to_nat n)) = tt}).
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a u) <<END
void *guwarray_set(int A, int c, void *d, void *l) {
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive uwarray_free : Fun(A:type)(n:word)(^ #unique l:<uwarray A (word_to_nat n)>).void :=
  fun(A:type)(n:word)(l:<uwarray A (word_to_nat n)>).voidi <<END
void guwarray_free(int A, int n, void *l) {
  // fprintf(stdout,"guwarray_free(%x).\n", l);
  carraway_free(l);
}
END.
