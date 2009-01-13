#include <limits.h>
gword_inc_t gword_inc(gword c) {
  return gmk_word_inc_t(c+1, (c == UINT_MAX));
}
