gcharvec ucvmod_f(void *b, void *a) {
  gmk_ucvmod_t2_struct *m = (gmk_ucvmod_t2_struct *)b;

  gcharvec l = m->arg1;
  gchar c = m->arg2;

  inc_gcharvec(l);
  /* do not dec l[c] first, since the function below already handed
     out that reference. */
  l[c]= a;
  dec_gucvmod_t2(m);
  return l;
}

inline gucvmod_t gucvmod(gtype A, gcharvec l, gchar c) {
  return gmk_ucvmod_t(A,l[c],type_name_gucvmod_t2,
		      gmk_ucvmod_t2(A,l,c), ucvmod_f);
}
