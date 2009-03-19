Include "unowned.w".

Attribute owned with gdrop_owned : Fun(A:type)(x:owned).void <<END
  #define gdrop_owned(A,x) 
END

Primitive inspect : Fun(!x:unowned).<owned x> <<END
  void *ginspect(void *x) {
    return x;
  }
END

Primitive inc_owned : Fun(!y:owned).unowned <<END
  void *ginc_owned(void *y) {
    inc(y);
    return y;
  }
END

Primitive owned_to_unowned : Fun(^y:owned).unowned <<END
  void *gowned_to_unowned(void *y) {
    inc(y);
    return y;
  }
END

Primitive clone_owned : Fun(! y:owned).<owned y> <<END
  void *gclone_owned(void *y) {
    return y;
  }
END

Primitive consume_owned : Fun(^ y:owned).void <<END
  #define gconsume_owned(y)  
END

Init ginit_unowned_owned : Fun(A:type)(! x:unowned)(y:owned).owned <<END
  #define ginit_unowned_owned(A,x,y) 
END

Init ginit_owned_owned : Fun(A:type)(! x:owned)(y:owned).owned <<END
  #define ginit_unowned_owned(A,x,y) 
END

Init ginit_owned_unowned : Fun(A:type)(! x:owned)(y:unowned).<owned x> <<END
  #define ginit_owned_unowned(A,x,y) 
END