typedef void *(*funtp_gmk_ucharvec)(void *);

inline gcharvec gmk_ucharvec(gtype A, gtype B, void *b, funtp_gmk_ucharvec f) {
  gcharvec h = (gcharvec)guru_alloc(sizeof(void *)*128);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = f(b);
  return h;
}
