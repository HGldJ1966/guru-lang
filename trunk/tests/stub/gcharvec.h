typedef void **gcharvec;

// unique, so no reference tracking is needed.

#define inc_gcharvec(x) 
#define dec_gcharvec(x) 
void *pinc_gcharvec(void *x) { return x; }
void pdec_gcharvec(void *x) { }
