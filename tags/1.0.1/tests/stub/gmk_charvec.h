gcharvec gmk_charvec(gtype A, void *a) {
  gcharvec h = (gcharvec)guru_alloc(sizeof(void *)*128);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = polyinc[A](a);
  return h;
}
