Include "owned.g".

ResourceType unique with
  Define primitive consume_unique : Fun(A:type)(^#unique x:A).void
    := fun(A:type)(x:A).voidi <<END
  inline void gconsume_unique(int A, void *x) {
    release(A,x);
  }
END.

% for unique things consuming no memory
ResourceType unique_point with
   Define primitive consume_unique_point : Fun(A:type)(^#unique_point x:A).void
    := fun(A:type)(x:A).voidi <<END
  inline void gconsume_unique_point(int A, int x) {}
END.

Init must_consume_scrutinee take_pointer ginit_unique_unique(#unique x)(#unique y).#unique <<END
  #define ginit_unique_unique(A,x,y) y
END.

Init ginit_unique_unique_point(#unique x)(#unique_point y).#unique_point <<END
  #define ginit_unique_unique_point(A,x,y) 1
END.

Init must_consume_scrutinee take_pointer ginit_unique_owned(#unique x)(#owned y).#owned <<END
  #define ginit_unique_owned(A,x,y) y
END.

Init must_consume_scrutinee take_pointer ginit_unique_unowned(#unique x)(#unowned y).#unowned <<END
  #define ginit_unique_unowned( A, x, y) y
END.

