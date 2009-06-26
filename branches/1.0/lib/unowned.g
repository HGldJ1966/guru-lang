ResourceType unowned with
  Define primitive consume_unowned : Fun(A:type)(^ #unowned r:A).void 
  := fun(A:type)(r:A).voidi <<END

  void *ginc(void *y) {
    inc(y);
    // fprintf(stdout,"ginc(%x) = %d\n", y, op(y) >> 8);
    return y;
  }

  #define gdec(A,y) gconsume_unowned(A,y)

  void gconsume_unowned(int A, void *r) {
    dec(r);
    // fprintf(stdout,"gdec(%x) = %d\n", r, op(r) >> 8);
    if (op(r) < 256)
      release(A,r);
  }
END.

Init ginit_unowned_unowned(#unowned x)(#unowned y).#unowned <<END
  void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END.

Define primitive inc : Fun(spec A:type)(! #unowned y:A).#unowned A := fun(A:type)(y:A).y <<END
// ginc included with resource type above
END.

Define primitive dec : Fun(A:type)(^#unowned y:A).void := fun(A:type)(y:A).voidi <<END
// gdec included with resource type above
END.

