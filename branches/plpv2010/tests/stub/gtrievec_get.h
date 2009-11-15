typedef void * (*funtp_trievec_get)(void *, gtrie);

inline void *gtrievec_get(gtype A, gvec l, gchar c, gtype B, gtype C,
			  void *b, funtp_trievec_get f) {
  return f(b,(gtrie)l[c]);
}
