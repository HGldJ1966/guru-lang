// produced by carraway

#include <stdio.h>

#include <stdlib.h>

void release(int tp, void *x, int clear);

#define carraway_malloc(x) malloc(x)
#define carraway_free(x) free(x)
#define guru_malloc(x) carraway_malloc(x)
#define guru_free(x) carraway_free(x)
/*********************************************************
 * Data types and resource types
 *********************************************************/
#include <limits.h>

#define ctor(x) (*((int *)x) & 255)
#define op(x) (*((int *)x))

void inc(void *x) {
  unsigned tmp = *((int *)x) | 255;
  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) + 256;
}

void dec(void *x) {
  unsigned tmp = *((int *)x) | 255;
  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) - 256;
}

/*********************************************************
 * consume_unowned
 *********************************************************/


  inline void *ginc(void *y) {
    inc(y);
    // fprintf(stdout,"ginc(%x) = %d\n", y, op(y) >> 8);
    return y;
  }

  #define gdec(A,y) gconsume_unowned(A,y)

  inline void gconsume_unowned(int A, void *r) {
    if (r == 0) return;
    dec(r);
    // fprintf(stdout,"gdec(%x) = %d\n", r, op(r) >> 8);
    if (op(r) < 256)
      release(A,r,1);
  }

/*********************************************************
 * consume_owned
 *********************************************************/

  inline void gconsume_owned(int A, void *x) { }

/*********************************************************
 * consume_unique
 *********************************************************/

  inline void gconsume_unique(int A, void *x) {
    release(A,x,0);
  }

/*********************************************************
 * consume_unique_point
 *********************************************************/

  inline void gconsume_unique_point(int A, int x) {}

/*********************************************************
 * Init functions
 *********************************************************/

  inline void *ginit_unowned_unowned(int A,void *x,void *y) {
    ginc(y);
    return y;
  }

  #define ginit_unowned_owned(A,x,y) y

  #define ginit_unowned_owned(A,x,y) y

  #define ginit_owned_unowned(A,x,y) y

  #define ginit_unique_unique(A,x,y) y

  #define ginit_unique_unique_point(A,x,y) 1

  #define ginit_unique_owned(A,x,y) y

  #define ginit_unique_unowned( A, x, y) y
/*********************************************************
 * Definitions
 *********************************************************/
/*********************************************************
 * pair
 *********************************************************/
#define gpair 1

#define op_gmkpair 0

typedef struct {
  int opval;
  void *gA_10;
  void *gB_2;
  void *ga_2;
  void *gb_2;
} gpair_gmkpair;

#define select_pair_mkpair_A(x) (((gpair_gmkpair *)x)->gA_10)
#define select_pair_mkpair_B(x) (((gpair_gmkpair *)x)->gB_2)
#define select_pair_mkpair_a(x) (((gpair_gmkpair *)x)->ga_2)
#define select_pair_mkpair_b(x) (((gpair_gmkpair *)x)->gb_2)

void clear_gpair_gmkpair(void *_x);
int free_gpair_gmkpair_len = 0;
void *free_gpair_gmkpair = (void *)0;

int clear_free_gpair_gmkpair_len = 0;
void *clear_free_gpair_gmkpair = (void *)0;

void delete_gpair_gmkpair(void *_x, int clear) {
  if (clear) {
    if (clear_free_gpair_gmkpair_len > 10) {
      clear_gpair_gmkpair(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gpair_gmkpair;
      clear_free_gpair_gmkpair = x;
      clear_free_gpair_gmkpair_len++;
    }
  }
  else {
    if (free_gpair_gmkpair_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gpair_gmkpair;
      free_gpair_gmkpair = x;
      free_gpair_gmkpair_len++;
    }
  }
}

void clear_gpair_gmkpair(void *_x) {
  gpair_gmkpair *x = (gpair_gmkpair *)_x;
  gconsume_unowned(x->gA_10, x->ga_2);
  gconsume_unowned(x->gB_2, x->gb_2);
}

void *gmkpair(void *gA_10, void *gB_2, void *ga_2, void *gb_2) {
  gpair_gmkpair *x;
  if (free_gpair_gmkpair) {
    x = (gpair_gmkpair *)free_gpair_gmkpair;
    free_gpair_gmkpair = ((void **)x)[0];
    free_gpair_gmkpair_len--;
  }
  else if (clear_free_gpair_gmkpair) {
    x = (gpair_gmkpair *)clear_free_gpair_gmkpair;
    clear_free_gpair_gmkpair = ((void **)x)[0];
    clear_free_gpair_gmkpair_len--;
    clear_gpair_gmkpair(x);
  }
  else
    x = (gpair_gmkpair *)carraway_malloc(sizeof(void *)*5);
  x->opval = 256 + op_gmkpair;
  x->gA_10 = gA_10;
  x->gB_2 = gB_2;
  x->ga_2 = ga_2;
  x->gb_2 = gb_2;
  return x;
}

void delete_gpair(void *x, int clear) {
  switch ctor(x) {
  case op_gmkpair: 
    delete_gpair_gmkpair(x,clear);
    break;

}
}

/*********************************************************
 * ulist
 *********************************************************/
#define gulist 2

#define op_gunil 0

#define op_gucons 1

typedef struct {
  int opval;
} gulist_gunil;

#define clear_gulist_gunil(x) 

int free_gulist_gunil_len = 0;
void *free_gulist_gunil = (void *)0;

int clear_free_gulist_gunil_len = 0;
void *clear_free_gulist_gunil = (void *)0;

void delete_gulist_gunil(void *_x, int clear) {
  if (clear) {
    if (clear_free_gulist_gunil_len > 10) {
      clear_gulist_gunil(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gulist_gunil;
      clear_free_gulist_gunil = x;
      clear_free_gulist_gunil_len++;
    }
  }
  else {
    if (free_gulist_gunil_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gulist_gunil;
      free_gulist_gunil = x;
      free_gulist_gunil_len++;
    }
  }
}

void *gunil() {
  gulist_gunil *x;
  if (free_gulist_gunil) {
    x = (gulist_gunil *)free_gulist_gunil;
    free_gulist_gunil = ((void **)x)[0];
    free_gulist_gunil_len--;
  }
  else if (clear_free_gulist_gunil) {
    x = (gulist_gunil *)clear_free_gulist_gunil;
    clear_free_gulist_gunil = ((void **)x)[0];
    clear_free_gulist_gunil_len--;
    clear_gulist_gunil(x);
  }
  else
    x = (gulist_gunil *)carraway_malloc(sizeof(void *)*1);
  x->opval = 256 + op_gunil;
  return x;
}

typedef struct {
  int opval;
  void *ga_4;
  void *gl_2;
} gulist_gucons;

#define select_ulist_ucons_a(x) (((gulist_gucons *)x)->ga_4)
#define select_ulist_ucons_l(x) (((gulist_gucons *)x)->gl_2)

void clear_gulist_gucons(void *_x);
int free_gulist_gucons_len = 0;
void *free_gulist_gucons = (void *)0;

int clear_free_gulist_gucons_len = 0;
void *clear_free_gulist_gucons = (void *)0;

void delete_gulist_gucons(void *_x, int clear) {
  if (clear) {
    if (clear_free_gulist_gucons_len > 10) {
      clear_gulist_gucons(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gulist_gucons;
      clear_free_gulist_gucons = x;
      clear_free_gulist_gucons_len++;
    }
  }
  else {
    if (free_gulist_gucons_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gulist_gucons;
      free_gulist_gucons = x;
      free_gulist_gucons_len++;
    }
  }
}

void clear_gulist_gucons(void *_x) {
  gulist_gucons *x = (gulist_gucons *)_x;
  gconsume_unowned(gulist, x->gl_2);
}

void *gucons(void *ga_4, void *gl_2) {
  gulist_gucons *x;
  if (free_gulist_gucons) {
    x = (gulist_gucons *)free_gulist_gucons;
    free_gulist_gucons = ((void **)x)[0];
    free_gulist_gucons_len--;
  }
  else if (clear_free_gulist_gucons) {
    x = (gulist_gucons *)clear_free_gulist_gucons;
    clear_free_gulist_gucons = ((void **)x)[0];
    clear_free_gulist_gucons_len--;
    clear_gulist_gucons(x);
  }
  else
    x = (gulist_gucons *)carraway_malloc(sizeof(void *)*3);
  x->opval = 256 + op_gucons;
  x->ga_4 = ga_4;
  x->gl_2 = gl_2;
  return x;
}

void delete_gulist(void *x, int clear) {
  switch ctor(x) {
  case op_gunil: 
    delete_gulist_gunil(x,clear);
    break;

  case op_gucons: 
    delete_gulist_gucons(x,clear);
    break;

}
}

/*********************************************************
 * nat
 *********************************************************/
#define gnat 3

#define op_gZ 0

#define op_gS 1

typedef struct {
  int opval;
} gnat_gZ;

#define clear_gnat_gZ(x) 

int free_gnat_gZ_len = 0;
void *free_gnat_gZ = (void *)0;

int clear_free_gnat_gZ_len = 0;
void *clear_free_gnat_gZ = (void *)0;

void delete_gnat_gZ(void *_x, int clear) {
  if (clear) {
    if (clear_free_gnat_gZ_len > 10) {
      clear_gnat_gZ(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gnat_gZ;
      clear_free_gnat_gZ = x;
      clear_free_gnat_gZ_len++;
    }
  }
  else {
    if (free_gnat_gZ_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gnat_gZ;
      free_gnat_gZ = x;
      free_gnat_gZ_len++;
    }
  }
}

void *gZ() {
  gnat_gZ *x;
  if (free_gnat_gZ) {
    x = (gnat_gZ *)free_gnat_gZ;
    free_gnat_gZ = ((void **)x)[0];
    free_gnat_gZ_len--;
  }
  else if (clear_free_gnat_gZ) {
    x = (gnat_gZ *)clear_free_gnat_gZ;
    clear_free_gnat_gZ = ((void **)x)[0];
    clear_free_gnat_gZ_len--;
    clear_gnat_gZ(x);
  }
  else
    x = (gnat_gZ *)carraway_malloc(sizeof(void *)*1);
  x->opval = 256 + op_gZ;
  return x;
}

typedef struct {
  int opval;
  void *gx_13;
} gnat_gS;

#define select_nat_S_x(x) (((gnat_gS *)x)->gx_13)

void clear_gnat_gS(void *_x);
int free_gnat_gS_len = 0;
void *free_gnat_gS = (void *)0;

int clear_free_gnat_gS_len = 0;
void *clear_free_gnat_gS = (void *)0;

void delete_gnat_gS(void *_x, int clear) {
  if (clear) {
    if (clear_free_gnat_gS_len > 10) {
      clear_gnat_gS(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gnat_gS;
      clear_free_gnat_gS = x;
      clear_free_gnat_gS_len++;
    }
  }
  else {
    if (free_gnat_gS_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gnat_gS;
      free_gnat_gS = x;
      free_gnat_gS_len++;
    }
  }
}

void clear_gnat_gS(void *_x) {
  gnat_gS *x = (gnat_gS *)_x;
  gconsume_unowned(gnat, x->gx_13);
}

void *gS(void *gx_13) {
  gnat_gS *x;
  if (free_gnat_gS) {
    x = (gnat_gS *)free_gnat_gS;
    free_gnat_gS = ((void **)x)[0];
    free_gnat_gS_len--;
  }
  else if (clear_free_gnat_gS) {
    x = (gnat_gS *)clear_free_gnat_gS;
    clear_free_gnat_gS = ((void **)x)[0];
    clear_free_gnat_gS_len--;
    clear_gnat_gS(x);
  }
  else
    x = (gnat_gS *)carraway_malloc(sizeof(void *)*2);
  x->opval = 256 + op_gS;
  x->gx_13 = gx_13;
  return x;
}

void delete_gnat(void *x, int clear) {
  switch ctor(x) {
  case op_gZ: 
    delete_gnat_gZ(x,clear);
    break;

  case op_gS: 
    delete_gnat_gS(x,clear);
    break;

}
}

/*********************************************************
 * vec
 *********************************************************/
#define gvec 4

#define op_gvecn 0

#define op_gvecc 1

typedef struct {
  int opval;
  void *gA_12;
} gvec_gvecn;

#define select_vec_vecn_A(x) (((gvec_gvecn *)x)->gA_12)

void clear_gvec_gvecn(void *_x);
int free_gvec_gvecn_len = 0;
void *free_gvec_gvecn = (void *)0;

int clear_free_gvec_gvecn_len = 0;
void *clear_free_gvec_gvecn = (void *)0;

void delete_gvec_gvecn(void *_x, int clear) {
  if (clear) {
    if (clear_free_gvec_gvecn_len > 10) {
      clear_gvec_gvecn(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gvec_gvecn;
      clear_free_gvec_gvecn = x;
      clear_free_gvec_gvecn_len++;
    }
  }
  else {
    if (free_gvec_gvecn_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gvec_gvecn;
      free_gvec_gvecn = x;
      free_gvec_gvecn_len++;
    }
  }
}

void clear_gvec_gvecn(void *_x) {
  gvec_gvecn *x = (gvec_gvecn *)_x;
}

void *gvecn(void *gA_12) {
  gvec_gvecn *x;
  if (free_gvec_gvecn) {
    x = (gvec_gvecn *)free_gvec_gvecn;
    free_gvec_gvecn = ((void **)x)[0];
    free_gvec_gvecn_len--;
  }
  else if (clear_free_gvec_gvecn) {
    x = (gvec_gvecn *)clear_free_gvec_gvecn;
    clear_free_gvec_gvecn = ((void **)x)[0];
    clear_free_gvec_gvecn_len--;
    clear_gvec_gvecn(x);
  }
  else
    x = (gvec_gvecn *)carraway_malloc(sizeof(void *)*2);
  x->opval = 256 + op_gvecn;
  x->gA_12 = gA_12;
  return x;
}

typedef struct {
  int opval;
  void *gA_14;
  void *ga_6;
  void *gl_4;
} gvec_gvecc;

#define select_vec_vecc_A(x) (((gvec_gvecc *)x)->gA_14)
#define select_vec_vecc_a(x) (((gvec_gvecc *)x)->ga_6)
#define select_vec_vecc_l(x) (((gvec_gvecc *)x)->gl_4)

void clear_gvec_gvecc(void *_x);
int free_gvec_gvecc_len = 0;
void *free_gvec_gvecc = (void *)0;

int clear_free_gvec_gvecc_len = 0;
void *clear_free_gvec_gvecc = (void *)0;

void delete_gvec_gvecc(void *_x, int clear) {
  if (clear) {
    if (clear_free_gvec_gvecc_len > 10) {
      clear_gvec_gvecc(_x);
      carraway_free(_x);
    }
    else {
      void **x = (void **)_x;
      x[0] = clear_free_gvec_gvecc;
      clear_free_gvec_gvecc = x;
      clear_free_gvec_gvecc_len++;
    }
  }
  else {
    if (free_gvec_gvecc_len > 10) 
      carraway_free(_x);
    else {
      void **x = (void **)_x;
      x[0] = free_gvec_gvecc;
      free_gvec_gvecc = x;
      free_gvec_gvecc_len++;
    }
  }
}

void clear_gvec_gvecc(void *_x) {
  gvec_gvecc *x = (gvec_gvecc *)_x;
  gconsume_unowned(x->gA_14, x->ga_6);
  gconsume_unowned(gvec, x->gl_4);
}

void *gvecc(void *gA_14, void *ga_6, void *gl_4) {
  gvec_gvecc *x;
  if (free_gvec_gvecc) {
    x = (gvec_gvecc *)free_gvec_gvecc;
    free_gvec_gvecc = ((void **)x)[0];
    free_gvec_gvecc_len--;
  }
  else if (clear_free_gvec_gvecc) {
    x = (gvec_gvecc *)clear_free_gvec_gvecc;
    clear_free_gvec_gvecc = ((void **)x)[0];
    clear_free_gvec_gvecc_len--;
    clear_gvec_gvecc(x);
  }
  else
    x = (gvec_gvecc *)carraway_malloc(sizeof(void *)*4);
  x->opval = 256 + op_gvecc;
  x->gA_14 = gA_14;
  x->ga_6 = ga_6;
  x->gl_4 = gl_4;
  return x;
}

void delete_gvec(void *x, int clear) {
  switch ctor(x) {
  case op_gvecn: 
    delete_gvec_gvecn(x,clear);
    break;

  case op_gvecc: 
    delete_gvec_gvecc(x,clear);
    break;

}
}

/*********************************************************
 * bool
 *********************************************************/
#define gbool 5

#define op_gff 0

#define op_gtt 1

#define gff() op_gff
#define clear_gbool_gff(x) 

#define gtt() op_gtt
#define clear_gbool_gtt(x) 

#define delete_gbool(x,clear) 

/*********************************************************
 * bv
 *********************************************************/
#define gbv gvec

/*********************************************************
 * delete_char
 *********************************************************/

  #define gdelete_char(c) 

/*********************************************************
 * char
 *********************************************************/
#define gchar 6

/*********************************************************
 * string
 *********************************************************/
#define gstring gulist

/*********************************************************
 * delete_stdio_t
 *********************************************************/

  #define gdelete_stdio_t(x) 

/*********************************************************
 * stdio_t
 *********************************************************/
#define gstdio_t 7

/*********************************************************
 * pb_in_t
 *********************************************************/
#define gpb_in_t gulist

/*********************************************************
 * cur_char
 *********************************************************/


  void *curc = 0;

  inline int gcur_char(void *s) {
     if (curc == 0) {
	int tmp = fgetc(stdin);
	curc = (tmp == -1 ? 0 : tmp);
     }
     return curc;
  }


