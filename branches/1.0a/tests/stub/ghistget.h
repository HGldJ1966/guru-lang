gnat ghistget(ghist h, gchar c) {
  gnat a = h[c];
  gnat_inc(a);
  return a;
}
