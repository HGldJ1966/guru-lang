Attribute unowned.

Primitive inc : Fun(^A:type)(y:unowned).unowned <<END
  void *ginc(void *y) {
    inc(y);
    return y;
  }
END

Primitive dec : Fun(A:type)(y:unowned).void <<END
  void gdec(tp A, void *y) {
    dec(y)
    if (cnt(y) == 0)
      release(A,y);
  }
END