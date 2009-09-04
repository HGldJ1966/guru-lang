ResourceType unowned with
  Define primitive consume_unowned : Fun(A:type)(^ #unowned r:A).void 
  := fun(A:type)(r:A).voidi <<END

  inline void *ginc(void *y) {
    inc(y);
    // fprintf(stdout,"ginc(%x) = %d\n", y, op(y) >> 8);
    return y;
  }

  #define gdec(A,y) gconsume_unowned(A,y)

  inline void gconsume_unowned(int A, void *r) {
    if (r == 0) return;
    dec(r);
    // fprintf(stdout,"gdec(%x) = %d\n", r, op(r) >> 8);
    if (op(r) < 256)
      release(A,r);
  }
END.

Init ginit_unowned_unowned(#unowned x)(#unowned y).#unowned <<END
  inline void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END.

Define primitive inc : Fun(spec A:type)(! #unowned y:A).#unowned A := fun(A:type)(y:A).y <<END
// ginc included with resource type above
END.

Define trusted inc_tot : Forall(A:type)(x:A).Exists(out:A).
  {(inc A x) = out} := truei.

Total inc inc_tot.

Define primitive dec : Fun(A:type)(^#unowned y:A).void := fun(A:type)(y:A).voidi <<END
// gdec included with resource type above
END.

