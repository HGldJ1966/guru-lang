ghist ghistupdate(ghist h, gchar c, gnat a) {
  gnat_dec(h[c]);
  h[c] = a;
  return h;
}
