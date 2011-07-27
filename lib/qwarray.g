%=============================================================================
% word-indexed arrays of unique data
%=============================================================================

Include trusted "word.g".
%Include trusted "unique_owned.g".

%Set "print_parsed".

Define primitive type_family_abbrev qwarray := fun(A:type)(n:word).<vec A (word_to_nat n)> <<END
#define gdelete_qwarray(x)
END.

Define primitive qwarray_new
 : Fun(spec A:type)(n:word)(f:Fun(i:word).A).#unique <qwarray A n> := 
  fun(spec A:type)(n:word)(f:Fun(i:word).A). (mkvec A a (word_to_nat n)) <<END
void *gqwarray_new(int n, void* (*f)(int), void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*n);
  int c;
  for (c = 0; c < n; c++)
    h[c] = f(c); // f is a generator function.
  return h;
}
END.
