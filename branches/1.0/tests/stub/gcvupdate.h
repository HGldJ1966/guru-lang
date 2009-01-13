gcharvec gcvupdate(gtype A, gchar c, void *d, gcharvec l) {
  polydec[A](l[c]);
  l[c] = d;
  return l;
}
