Attribute unowned with gdrop_unowned : Fun(A:type)(^ r:unowned).void <<END
#include <values.h>

#define ctor(x) (*((int *)x) & 255)
#define op(x) (*((int *)x))

void inc(void *x) {
  unsigned tmp = *((int *)x) | 255;
  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) + 256;
}

void dec(void *x) {
  unsigned tmp = *((int *)x) | 255;
  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) - 256;
}

  void gdrop_unowned(int A, void *r) {
    dec(r);
    if (op(r) < 256)
      release(A,r);
  }
END

Primitive inc : Fun(y:unowned).unowned <<END
  void *ginc(void *y) {
    inc(y);
    return y;
  }
END

Primitive dec : Fun(A:type)(y:unowned).void <<END
  void gdec(int A, void *y) {
    gdrop_unowned(A,y);
  }
END

Init ginit_unowned_unowned : Fun(A:type)(! x:unowned)(y:unowned).unowned <<END
  void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }
END