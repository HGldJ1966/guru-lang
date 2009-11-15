ResourceType unowned with consume_unowned : Fun(A:type)(^ r:unowned).void <<END
  void gconsume_unowned(int A, void *r) {
    dec(r);
    if (op(r) < 256)
      release(A,r);
  }
END

Primitive inc : Fun(!y:unowned).unowned <<END
  void *ginc(void *y) {
    inc(y);
    return y;
  }
END

Primitive dec : Fun(A:type)(^y:unowned).void <<END
  #define gdec(A,y) gconsume_unowned(A,y)
END

Init ginit_unowned_unowned : Fun(A:type)(! x:unowned)(y:unowned).unowned <<END
  void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END