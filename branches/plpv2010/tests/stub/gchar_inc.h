gchar_inc_t gchar_inc(gchar c) {
  int t = c+1;
  return gmk_char_inc_t((char)t, (t > 127));
}
