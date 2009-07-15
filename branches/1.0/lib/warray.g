%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique.g".

%Set "print_parsed".

Define primitive type_family_abbrev warray := fun(A:type)(n:word).<vec A (to_nat wordlen n)> <<END
#define gdelete_warray(x)
END.

Define primitive warray_new
 : Fun(spec A:type)(#untracked n:word)(^#owned a:A).#unique <warray A n> := 
  fun(A:type)(n:word)(a:A). (mkvec A a (to_nat wordlen n)) <<END
void *gwarray_new(int n, void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*128);
  // fprintf(stdout,"gmk_warray(%x).\n", h);
  int c;
  for (c = 0; c <= n; c++)
    h[c] = ginc(a); 
  return h;
}
END.

Define primitive warray_get
   : Fun(spec A:type)(spec n:word)(!#unique l:<warray A n>)
        (#untracked i:word)
        (u:{(lt (to_nat i) (to_nat n)) = tt}). #<owned l> A := 
  fun(A:type)(spec n:word)(l:<warray A n>)(i:word)(u:{(lt (to_nat i) (to_nat n)) = tt}). 
    (vec_get A (to_nat wordlen n) l (to_nat wordlen i) u) <<END
void *gwarray_get(void *l, int i) {
  return ((void **)l)[i];
}
END.

Define primitive warray_mod 
  : Fun(A:type)(#untracked i:word)(a:A)(spec n:word)(#unique l:<warray A n>)
       (u:{(lt (to_nat i) (to_nat n)) = tt}). #unique <warray A n> :=
  fun(A:type)(i:word)(a:A)(spec n:word)(l:<warray A n>)(u:{(lt (to_nat i) (to_nat n)) = tt}).
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a u) <<END
void *gwarray_mod(int A, int c, void *d, void *l) {
  gdec(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive warray_free : Fun(A:type)(#untracked n:word)(^ #unique l:<warray A n>).void :=
  fun(A:type)(n:word)(l:<warray A n>).voidi <<END
void gwarray_free(int A, int n, void *l) {
  int c;
  // fprintf(stdout,"gwarray_free(%x).\n", l);
  for (c = 0; c <= n; c++) 
    gdec(A,((void **)l)[c]);
  carraway_free(l);
}
END.
