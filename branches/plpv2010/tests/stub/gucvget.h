typedef void * (*funtp_ucvget)(void *, void *);

inline void *gucvget(gtype A, gcharvec l, gchar c, gtype B, gtype C,
		     void *b, funtp_ucvget f) {
  return f(b,(gtrie)l[c]);
}
