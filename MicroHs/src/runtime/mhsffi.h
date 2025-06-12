#include <inttypes.h>
#include <stdlib.h>
#include <time.h>

#if INTPTR_MAX == 0x7fff
#define WORD_SIZE 16
#elif INTPTR_MAX == 0x7fffffff
#define WORD_SIZE 32
#elif INTPTR_MAX == 0x7fffffffffffffff
#define WORD_SIZE 64
#else
#error Unknown WORD_SIZE
#endif

#if WORD_SIZE == 64
typedef double flt_t;
#elif WORD_SIZE == 32
typedef float flt_t;
#elif WORD_SIZE == 16
typedef uint16_t flt_t;         /* No floats, but we need something */
#else
#error Unknown WORD_SIZE
#endif

typedef void (*HsFunPtr)(void);

typedef int from_t;
typedef from_t (*funptr_t)(int);
struct ffi_entry {
  const char *ffi_name;
  int         ffi_arity;
  funptr_t    ffi_fun;
};
extern struct ffi_entry *xffi_table;

from_t mhs_from_Double(intptr_t, int, flt_t);
from_t mhs_from_FloatW(intptr_t, int, flt_t);
from_t mhs_from_Int(intptr_t, int, intptr_t);
from_t mhs_from_Word(intptr_t, int, uintptr_t);
from_t mhs_from_Word8(intptr_t, int, uintptr_t);
from_t mhs_from_Ptr(intptr_t, int, void *);
from_t mhs_from_FunPtr(intptr_t, int, HsFunPtr);
from_t mhs_from_CChar(intptr_t, int, char);
from_t mhs_from_CSChar(intptr_t, int, signed char);
from_t mhs_from_CUChar(intptr_t, int, unsigned char);
from_t mhs_from_CShort(intptr_t, int, short);
from_t mhs_from_CUShort(intptr_t, int, unsigned short);
from_t mhs_from_CInt(intptr_t, int, int);
from_t mhs_from_CUInt(intptr_t, int, unsigned int);
from_t mhs_from_CLong(intptr_t, int, long);
from_t mhs_from_CULong(intptr_t, int, unsigned long);
from_t mhs_from_CLLong(intptr_t, int, long long);
from_t mhs_from_CULLong(intptr_t, int, unsigned long long);
from_t mhs_from_CSize(intptr_t, int, size_t);
from_t mhs_from_CTime(intptr_t, int, time_t); /* XXX wrong */
// not on MacOS void mhs_from_CSSize(intptr_t, int, ssize_t);
from_t mhs_from_CIntPtr(intptr_t, int, intptr_t);
from_t mhs_from_CUIntPtr(intptr_t, int, uintptr_t);
from_t mhs_from_Unit(intptr_t, int);

flt_t              mhs_to_Double(intptr_t, int);
flt_t              mhs_to_FloatW(intptr_t, int);
intptr_t           mhs_to_Int(intptr_t, int);
uintptr_t          mhs_to_Word(intptr_t, int);
uint8_t            mhs_to_Word8(intptr_t, int);
void*              mhs_to_Ptr(intptr_t, int);
HsFunPtr           mhs_to_FunPtr(intptr_t, int);
char               mhs_to_CChar(intptr_t, int);
signed char        mhs_to_CSChar(intptr_t, int);
unsigned char      mhs_to_CUChar(intptr_t, int);
short              mhs_to_CShort(intptr_t, int);
unsigned short     mhs_to_CUShort(intptr_t, int);
int                mhs_to_CInt(intptr_t, int);
unsigned int       mhs_to_CUInt(intptr_t, int);
long               mhs_to_CLong(intptr_t, int);
unsigned long      mhs_to_CULong(intptr_t, int);
long long          mhs_to_CLLong(intptr_t, int);
unsigned long long mhs_to_CULLong(intptr_t, int);
size_t             mhs_to_CSize(intptr_t, int);
time_t             mhs_to_CTime(intptr_t, int); /* XXX wrong */
// ssize_t            mhs_to_CSSize(intptr_t, int);
intptr_t           mhs_to_CIntPtr(intptr_t, int);
uintptr_t          mhs_to_CUIntPtr(intptr_t, int);
