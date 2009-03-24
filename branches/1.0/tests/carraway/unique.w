Include "owned.w".

Attribute unique with gdrop_unique : Fun(A:type)(^x:unique).void <<END
  void gdrop_unique(int A, void *x) {
    release(A,x);
  }
END

Init ginit_unique_unique : Fun(A:type)(! x:unique)(y:unique).unique <<END
  #define ginit_unowned_unique(A,x,y) y
END

Init ginit_unique_owned : Fun(A:type)(! x:unique)(y:owned).owned <<END
  #define ginit_unowned_unique(A,x,y) y
END

Init ginit_unique_unowned : Fun(A:type)(! x:unique)(y:unowned).unowned <<END
  void *ginit_unique_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END