Attribute unowned with gdrop_unowned : Fun(A:type)(r:unowned).void <<END
  void gdrop_unowned(int A)(void *r) {
    dec(y)
    if (cnt(y) == 0)
      release(A,y);
  }
END

Primitive inc : Fun(y:unowned).unowned <<END
  void *ginc(void *y) {
    inc(y);
    return y;
  }
END

Primitive dec : Fun(A:type)(y:unowned).void <<END
  void gdec(tp A, void *y) {
    gdrop_unowned(A,y);
  }
END

Init ginit_unowned_unowned : Fun(A:type)(! x:unowned)(y:unowned).unowned <<END
  void ginit_unowned_unowned(int A)(void *x)(void *y) {
    ginc(y);
  }
END