gvec trievec_mod_f(void *b, void *a) {
  gmk_ucvmod_t2_struct *m = (gmk_ucvmod_t2_struct *)b;

  gvec l = m->arg1;
  gchar c = m->arg2;

  gvec_inc(l);
  /* do not dec l[c] first, since the function below already handed
     out that reference. */
  l[c]= a;
  gucvmod_t2_dec(m);
  return l;
}

inline gucvmod_t gtrievec_mod(gtype A, gvec l, gchar c) {
  return gmk_ucvmod_t(A,l[c],(gtype)10 /*gucvmod_t2*/,
		      gmk_ucvmod_t2(A,l,c), trievec_mod_f);
}
