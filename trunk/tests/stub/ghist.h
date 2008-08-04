typedef gnat *ghist;

// ghist's are unique, so no reference tracking is needed.

#define inc_ghist(x) 
#define dec_ghist(x) 
void *pinc_ghist(void *x) { return x; }
void pdec_ghist(void *x) { }
