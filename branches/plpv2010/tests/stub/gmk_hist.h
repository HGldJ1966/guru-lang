ghist gmk_hist(gnat a) {
  ghist h = (ghist)guru_alloc(sizeof(gnat)*128);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = gnat_inc(a);
  gnat_dec(a);
  return h;
}
