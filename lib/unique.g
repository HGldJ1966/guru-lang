Include "owned.g".

ResourceType unique with
  Define primitive consume_unique : Fun(A:type)(^#unique x:A).void
    := fun(A:type)(x:A).voidi <<END
  void gconsume_unique(int A, void *x) {
    release(A,x);
  }
END.

Init ginit_unique_unique(#unique x)(#unique y).#unique <<END
  #define ginit_unowned_unique(A,x,y) y
END.

Init ginit_unique_owned(#unique x)(#owned y).#owned <<END
  #define ginit_unowned_unique(A,x,y) y
END.

Init ginit_unique_unowned(#unique x)(#unowned y).#unowned <<END
  void *ginit_unique_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END.