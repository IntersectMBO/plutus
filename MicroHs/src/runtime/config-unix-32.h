#include "config-unix-64.h"

//#undef WORD_SIZE
//#define WORD_SIZE 32

#undef FFS
#if _POSIX_VERSION >= 200112L
#define FFS ffs
#endif

