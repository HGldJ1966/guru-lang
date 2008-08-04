typedef gtrie(*funtp_gmk_trievec)(void *b);

inline gvec gmk_trievec(gtype A, gtype B, void *b, funtp_gmk_trievec f) {
  gvec h = (gvec)guru_alloc(sizeof(void *)*128);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = f(b);
  return h;
}
