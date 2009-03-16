Include "unowned.g".

Attribute owned.

Primitive inspect : Fun(^A:type)(!x:unowned).<owned x> <<END
  void *ginspect(void *x) {
    return x;
  }
END

Primitive inc2 : Fun(^A:type)(^B:type)(^ ! x:unowned)(y:<owned x>).unowned <<END
  void *ginc2(void *y) {
    inc(y);
    return y;
  }
END

Primitive drop : Fun(^A:type)(^B:type)(^ ! x:unowned)(y:<owned x>).void <<END
  void drop(void *y) {} 
END