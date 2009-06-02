ResourceType unowned with
  Define primitive consume_unowned : Fun(A:type)(^ #unowned r:A).void 
  := fun(A:type)(r:A).voidi <<END
  void gconsume_unowned(int A, void *r) {
    dec(r);
    if (op(r) < 256)
      release(A,r);
  }
END.

Define primitive inc : Fun(spec A:type)(! #unowned y:A).#unowned A := fun(A:type)(y:A).y <<END
  void *ginc(void *);
END.

Define primitive dec : Fun(A:type)(^#unowned y:A).void := fun(A:type)(y:A).voidi <<END
  #define gdec(A,y) gconsume_unowned(A,y)
END.

Init ginit_unowned_unowned(#unowned x)(#unowned y).#unowned <<END
  void *ginc(void *y) {
    inc(y);
    return y;
  }

  void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END.