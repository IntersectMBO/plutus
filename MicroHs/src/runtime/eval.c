/* Copyright 2023,2024,2025 Lennart Augustsson
 * See LICENSE file for full license.
 */
#if !defined(WANT_GMP)
#define WANT_GMP 0
#endif

#include <inttypes.h>
#if WANT_STDIO
#include <stdio.h>
#include <locale.h>
#endif  /* WANT_STDIO */
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <setjmp.h>
#if WANT_MATH
#include <math.h>
#endif  /* WANT_MATH */
#if WANT_DIR
#include <dirent.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>
#endif  /* WANT_DIR */
#if WANT_TIME
#include <time.h>
#endif
#if WANT_GMP
#include <gmp.h>
#endif
#if WANT_SIGINT
#include <signal.h>
#endif

#if WANT_MD5
#include "md5.h"
#endif

#if !defined(WANT_LZ77)
#define WANT_LZ77 1
#endif

#if !defined(WANT_RLE)
#define WANT_RLE 1
#endif

#if !defined(WANT_BWT)
#define WANT_BWT 1
#endif

#if WANT_LZ77
size_t lz77d(uint8_t *src, size_t srclen, uint8_t **bufp);
size_t lz77c(uint8_t *src, size_t srclen, uint8_t **bufp);
#endif

#if defined(__GNUC__) && __GNUC__ >= 14 && defined(__aarch64__)
#define REGISTER(dcl, reg) register dcl asm(#reg)
#else
#define REGISTER(dcl, reg) dcl
#endif

#include "mhsffi.h"
struct ffi_entry ffi_table[];
int num_ffi;
#define FFI_IX(i) ((i) < num_ffi ? ffi_table[i] : xffi_table[i - num_ffi])

//#include "config.h"

#if WANT_STDIO
#define THREAD_DEBUG 1
#else
#define THREAD_DEBUG 0
#endif

#define VERSION "v8.0\n"

typedef intptr_t value_t;       /* Make value the same size as pointers, since they are in a union */
#define PRIvalue PRIdPTR
typedef uintptr_t uvalue_t;     /* Make unsigned value the same size as pointers, since they are in a union */
#define PRIuvalue PRIuPTR
typedef uintptr_t heapoffs_t;   /* Heap offsets */
#define PRIheap PRIuPTR
typedef uintptr_t tag_t;        /* Room for tag, low order bit indicates AP/not-AP */
typedef intptr_t stackptr_t;    /* Index into stack */

typedef uintptr_t counter_t;    /* Statistics counter, can be smaller since overflow doesn't matter */
#define PRIcounter PRIuPTR
typedef uintptr_t bits_t;       /* One word of bits */

#if !defined(MALLOC)
#define MALLOC malloc
#endif

#if !defined(REALLOC)
#define REALLOC realloc
#endif

#if !defined(CALLOC)
#define CALLOC calloc
#endif

#if !defined(FREE)
#define FREE free
#endif

#if !defined(EXIT)
#define EXIT exit
#endif

#if !defined(PRINT)
#define PRINT printf
#endif

#if !defined(MAIN)
#define MAIN int main(int argc, char **argv)
#endif

#if !defined(PCOMMA)
#define PCOMMA "'"
#endif  /* !defined(PCOMMA) */

#if !defined(GETRAW)
int GETRAW(void) { return -1; }
#endif  /* !defined(getraw) */

#if !defined(GETTIMEMILLI)
value_t GETTIMEMILLI(void) { return 0; }
#endif  /* !define(GETTIMEMILLI) */

#if !defined(GETCPUTIME)
void GETCPUTIME(long *sec, long *usec) { return 0; }
#endif  /* !define(GETCPUTIME) */

#if !defined(INLINE)
#define INLINE inline
#endif  /* !define(INLINE) */

#if !defined(NORETURN)
/*#define NORETURN [[noreturn]]*/
#define NORETURN _Noreturn
#endif /* !defined(NORETURN) */

NORETURN void memerr(void);

void *
mmalloc(size_t s)
{
  void *p = MALLOC(s);
  if (!p)
    memerr();
  return p;
}

void *
mrealloc(void *q, size_t s)
{
  void *p = REALLOC(q, s);
  if (!p)
    memerr();
  return p;
}

void *
mcalloc(size_t n, size_t s)
{
  void *p = CALLOC(n, s);
  if (!p)
    memerr();
  return p;
}

#if !defined(TMPNAME)
/* This is a really bad implementation, since it doesn't check for anything. */
char* TMPNAME(const char* pre, const char* post) {
  char *s = mmalloc(strlen(pre) + 3 + strlen(post) + 1);
  strcpy(s, pre);
  strcat(s, "TMP");
  strcat(s, post);
  return s;
}
#endif

#if !defined(FFS)
/* This is pretty bad, could use deBruijn multiplication instead. */
int
FFS(bits_t x)
{
  int i;
  if (!x)
    return 0;
  for(i = 1; !(x & 1); x >>= 1, i++)
    ;
  return i;
}
#endif  /* !defined(FFS) */

#if defined(__has_builtin)

#if __has_builtin(__builtin_popcountl)
#define BUILTIN_POPCOUNT
#endif

#endif

#if !defined(POPCOUNT)
uvalue_t POPCOUNT(uvalue_t x) {
#if defined(BUILTIN_POPCOUNT)
  return __builtin_popcountl(x);
#else
  uvalue_t count = 0;
  while (x) {
    x = x & (x - 1); // clear lowest 1 bit
    count += 1;
  }
  return count;
#endif
}
#endif

#if defined(__GNUC__)
#define BUILTIN_CLZ
#elif defined(__clang__)

#if __has_builtin(__builtin_clzl)
#define BUILTIN_CLZ
#endif

#endif


#if !defined(CLZ)
uvalue_t CLZ(uvalue_t x) {
#if defined(BUILTIN_CLZ)
  if (x == 0) return WORD_SIZE;
  return __builtin_clzl(x);
#else
  value_t count = WORD_SIZE;
  while (x) {
    x = x >> 1;
    count -= 1;
  }
  return count;
#endif
}
#endif

#if defined(__has_builtin)

#if __has_builtin(__builtin_ctzl)
#define BUILTIN_CTZ
#endif

#endif


#if !defined(CTZ)
uvalue_t CTZ(uvalue_t x) {
  if (x == 0) return WORD_SIZE;
#if defined(BUILTIN_CLZ)
  return __builtin_ctzl(x);
#else
  uvalue_t count = 0;
  while ((x & 1) == 0) {
    x = x >> 1;
    count += 1;
  }
  return count;
#endif
}
#endif

#if !defined(WANT_ARGS)
#define WANT_ARGS 1
#endif

#if !defined(COUNT)
#define COUNT(n) ++(n)
#endif

value_t
iswindows(void)
{
#if defined(ISWINDOWS)
  return 1;
#else
  return 0;
#endif
}

/***************************************/

/* Keep permanent nodes for LOW_INT <= i < HIGH_INT */
#define LOW_INT (-10)
#define HIGH_INT 256

#if !defined(HEAP_CELLS)
#define HEAP_CELLS 50000000
#endif

#if !defined(STACK_SIZE)
#define STACK_SIZE 100000
#endif

#if !defined(ERR)
#if WANT_STDIO
#define ERR(s)    do { fprintf(stderr,"ERR: "s"\n");   EXIT(1); } while(0)
#define ERR1(s,a) do { fprintf(stderr,"ERR: "s"\n",a); EXIT(1); } while(0)
#else  /* WANT_STDIO */
#define ERR(s) EXIT(1)
#define ERR1(s,a) EXIT(1)
#endif  /* WANT_STDIO */
#endif  /* !define(ERR) */

enum node_tag { T_FREE, T_IND, T_AP, T_INT, T_DBL, T_PTR, T_FUNPTR, T_FORPTR, T_BADDYN, T_ARR, T_THID, T_MVAR,
                T_S, T_K, T_I, T_B, T_C,
                T_A, T_Y, T_SS, T_BB, T_CC, T_P, T_R, T_O, T_U, T_Z, T_J,
                T_K2, T_K3, T_K4, T_CCB,
                T_ADD, T_SUB, T_MUL, T_QUOT, T_REM, T_SUBR, T_UQUOT, T_UREM, T_NEG,
                T_AND, T_OR, T_XOR, T_INV, T_SHL, T_SHR, T_ASHR,
                T_POPCOUNT, T_CLZ, T_CTZ,
                T_EQ, T_NE, T_LT, T_LE, T_GT, T_GE, T_ULT, T_ULE, T_UGT, T_UGE, T_ICMP, T_UCMP,
                T_FPADD, T_FP2P, T_FPNEW, T_FPFIN, // T_FPSTR,
                T_FP2BS, T_BS2FP,
                T_TOPTR, T_TOINT, T_TODBL, T_TOFUNPTR,
                T_BININT2, T_BININT1, T_UNINT1,
                T_BINDBL2, T_BINDBL1, T_UNDBL1,
                T_BINBS2, T_BINBS1,
                T_ISINT,
#if WANT_FLOAT
                T_FADD, T_FSUB, T_FMUL, T_FDIV, T_FNEG, T_ITOF,
                T_FEQ, T_FNE, T_FLT, T_FLE, T_FGT, T_FGE, T_FSHOW, T_FREAD,
#endif
                T_ARR_ALLOC, T_ARR_COPY, T_ARR_SIZE, T_ARR_READ, T_ARR_WRITE, T_ARR_EQ,
                T_RAISE, T_SEQ, T_EQUAL, T_COMPARE, T_RNF,
                T_TICK,
                T_IO_BIND, T_IO_THEN, T_IO_RETURN,
                T_IO_SERIALIZE, T_IO_DESERIALIZE,
                T_IO_GETARGREF,
                T_IO_PERFORMIO, T_IO_PRINT, T_CATCH, T_CATCHR,
                T_IO_CCALL,
                T_IO_GC, T_IO_STATS,
                T_DYNSYM,
                T_IO_FORK, T_IO_THID, T_THNUM, T_IO_THROWTO, T_IO_YIELD,
                T_IO_NEWMVAR,
                T_IO_TAKEMVAR, T_IO_PUTMVAR, T_IO_READMVAR,
                T_IO_TRYTAKEMVAR, T_IO_TRYPUTMVAR, T_IO_TRYREADMVAR,
                T_IO_THREADDELAY, T_IO_THREADSTATUS,
                T_IO_GETMASKINGSTATE, T_IO_SETMASKINGSTATE,
                T_NEWCASTRINGLEN, T_PACKCSTRING, T_PACKCSTRINGLEN,
                T_BSAPPEND, T_BSEQ, T_BSNE, T_BSLT, T_BSLE, T_BSGT, T_BSGE, T_BSCMP,
                T_BSPACK, T_BSUNPACK, T_BSREPLICATE, T_BSLENGTH, T_BSSUBSTR, T_BSINDEX,
                T_BSFROMUTF8, T_BSTOUTF8, T_BSHEADUTF8, T_BSTAILUTF8,
                T_BSAPPENDDOT,
                T_IO_PP,           /* for debugging */
                T_IO_STDIN, T_IO_STDOUT, T_IO_STDERR,
                T_LAST_TAG,
};
/* Most entries are initialized from the primops table. */
static const char* tag_names[T_LAST_TAG+1] =
  { "FREE", "IND", "AP", "INT", "DBL", "PTR", "FUNPTR", "FORPTR", "BADDYN", "ARR", "THID", "MVAR" };

struct ioarray;
struct bytestring;
struct forptr;
struct mthread;
struct mvar;

typedef struct node {
  union {
    struct node *uufun;
    intptr_t     uuifun;
    tag_t        uutag;             /* LSB=1 indicates that this is a tag, LSB=0 that this is a T_AP node */
  } ufun;
  union {
    struct node    *uuarg;
    value_t         uuvalue;
    flt_t           uufloatvalue;
    const char     *uucstring;
    void           *uuptr;
    HsFunPtr        uufunptr;
    struct ioarray *uuarray;
    struct forptr  *uuforptr;      /* foreign pointers and byte arrays */
    struct mthread *uuthread;
    struct mvar    *uumvar;
  } uarg;
} node;
#define BIT_TAG   1
#define BIT_IND   2
#define BIT_NOTAP (BIT_TAG | BIT_IND)
#define TAG_SHIFT 2

typedef struct node* NODEPTR;
#define NIL 0
#define HEAPREF(i) &cells[(i)]
#define GETTAG(p) ((p)->ufun.uutag & BIT_NOTAP ? ( (p)->ufun.uutag & BIT_IND ? T_IND : (int)((p)->ufun.uutag >> TAG_SHIFT) ) : T_AP)
#define SETTAG(p,t) do { if (t != T_AP) { if (t == T_IND) { (p)->ufun.uutag = BIT_IND; } else { (p)->ufun.uutag = ((t) << TAG_SHIFT) | BIT_TAG; } } } while(0)
#define GETVALUE(p) (p)->uarg.uuvalue
#define GETDBLVALUE(p) (p)->uarg.uufloatvalue
#define SETVALUE(p,v) (p)->uarg.uuvalue = v
#define SETDBLVALUE(p,v) (p)->uarg.uufloatvalue = v
#define FUN(p) (p)->ufun.uufun
#define ARG(p) (p)->uarg.uuarg
#define CSTR(p) (p)->uarg.uucstring
#define PTR(p) (p)->uarg.uuptr
#define FUNPTR(p) (p)->uarg.uufunptr
#define FORPTR(p) (p)->uarg.uuforptr
#define BSTR(p) (p)->uarg.uuforptr->payload
#define ARR(p) (p)->uarg.uuarray
#define THR(p) (p)->uarg.uuthread
#define MVAR(p) (p)->uarg.uumvar
#define ISINDIR(p) ((p)->ufun.uuifun & BIT_IND)
#define GETINDIR(p) ((struct node*) ((p)->ufun.uuifun & ~BIT_IND))
#define SETINDIR(p,q) do { (p)->ufun.uuifun = (intptr_t)(q) | BIT_IND; } while(0)
#define NODE_SIZE sizeof(node)
#define ALLOC_HEAP(n) do { cells = mmalloc(n * sizeof(node)); } while(0)
#define LABEL(n) ((heapoffs_t)((n) - cells))
node *cells;                 /* All cells */

/*
 * byte arrays
 */
struct bytestring {
  size_t size;
  void *string;
};

/*
 * Arrays are allocated with malloc()/free().
 * During GC they are marked, and all elements in the array are
 * recursively marked.
 * At the end of the the mark phase there is a scan of all
 * arrays, and the unmarked ones are freed.
 */
struct ioarray {
  struct ioarray *next;         /* all ioarrays are linked together */
  int permanent;                /* this array should never be GC-ed */
  size_t marked;                /* marked during GC */
  size_t size;                  /* number of elements in the array */
  NODEPTR array[1];             /* actual size may be bigger */
};
struct ioarray *array_root = 0; /* root of all allocated arrays, linked by next */

enum fptype {
  FP_FORPTR = 0,                /* a regular foreign pointer to unknown memory */
  FP_BSTR,                      /* a bytestring */
  FP_MPZ,                       /* a GMP MPZ pointer */
};

/*
 * A Haskell ForeignPtr has a normal pointer, and a finalizer
 * function that is to be called when there are no more references
 * to the ForeignPtr.
 * A complication is that using plusForeignPtr creates a new
 * ForeignPtr that must share the same finalizer.
 * There is one struct forptr for each ForeignPtr.  It has pointer
 * to the actual data, and to a struct final which is shared between
 * all ForeignPtrs that have been created with plusForeignPtr.
 * During GC the used bit is set for any references to the forptr.
 * The scan phase will traverse the struct final chain and run
 * the finalizer, and free associated structs.
 */
struct final {
  struct final  *next;      /* the next finalizer */
  HsFunPtr       final;     /* function to call to release resource */
  void          *arg;       /* argument to final when called */
  size_t         size;      /* size of memory, if known, otherwise NOSIZE */
#define NOSIZE ~0           /* used as the size in payload for actual foreign pointers */
  struct forptr *back;      /* back pointer to the first forptr */
  short          marked;    /* mark bit for GC */
  enum fptype    fptype;    /* what kind of foreign pointer */
};

/*
 * Foreign pointers are also used to represent bytestrings.
 * The difference between a foreign pointer and a bytestring
 * is that we can serialize the latter.
 * The size field is non-zero only for bytestrings.
 */
struct forptr {
  struct forptr *next;       /* the next ForeignPtr that shares the same finalizer */
  struct final  *finalizer;  /* the finalizer for this ForeignPtr */
  struct bytestring payload; /* the actual pointer to allocated data, and maybe a size */
  //  char          *desc;
};
struct final *final_root = 0;   /* root of all allocated foreign pointers, linked by next */

//REGISTER(counter_t num_reductions,r19);
counter_t num_reductions = 0;
counter_t num_alloc = 0;
counter_t num_gc = 0;
counter_t num_yield = 0;
counter_t num_resched = 0;
counter_t num_thread_reap = 0;
counter_t num_mvar_alloc = 0;
counter_t num_mvar_free = 0;
uintptr_t gc_mark_time = 0;
uintptr_t gc_scan_time = 0;
uintptr_t run_time = 0;

#define MAIN_THREAD 1
uvalue_t num_thread_create = MAIN_THREAD;

#define MAXSTACKDEPTH 0
#if MAXSTACKDEPTH
stackptr_t max_stack_depth = 0;
counter_t max_c_stack = 0;
counter_t cur_c_stack = 0;
#define MAXSTACK if (stack_ptr > max_stack_depth) max_stack_depth = stack_ptr
#else
#define MAXSTACK
#endif

NODEPTR *topnode;
NODEPTR atptr;

REGISTER(NODEPTR *stack,r20);
REGISTER(stackptr_t stack_ptr,r21);
#if STACKOVL
#define PUSH(x) do { if (stack_ptr >= stack_size-2) stackerr(); stack[++stack_ptr] = (x); MAXSTACK; } while(0)
#else  /* STACKOVL */
#define PUSH(x) do {                                            stack[++stack_ptr] = (x); MAXSTACK; } while(0)
#endif  /* STACKOVL */
#define TOP(n) stack[stack_ptr - (n)]
#define POP(n) stack_ptr -= (n)
#define POPTOP() stack[stack_ptr--]
#define GCCHECK(n) gc_check((n))
#define CLEARSTK() do { stack_ptr = -1; } while(0)
#define GCCHECKSAVE(p, n) do { PUSH(p); GCCHECK(n); (p) = TOP(0); POP(1); } while(0)

heapoffs_t heap_size;       /* number of heap cells */
heapoffs_t heap_start;      /* first location in heap that needs GC */
REGISTER(stackptr_t stack_size,r22);      /* number of stack slots */

counter_t num_marked;
counter_t max_num_marked = 0;
counter_t num_free;
counter_t num_arr_alloc;
counter_t num_arr_free;
counter_t num_fin_alloc;
counter_t num_fin_free;
counter_t num_bs_alloc;
counter_t num_bs_alloc_max;
counter_t num_bs_free;
counter_t num_bs_bytes;
counter_t num_bs_inuse;
counter_t num_bs_inuse_max;

#define BITS_PER_WORD (sizeof(bits_t) * 8)
bits_t *free_map;             /* 1 bit per node, 0=free, 1=used */
heapoffs_t free_map_nwords;
heapoffs_t next_scan_index;

int want_gc_red = 0;

NORETURN void
memerr(void)
{
  ERR("Out of memory");
  EXIT(1);
}

NORETURN
void
stackerr(void)
{
  ERR("stack overflow");
  EXIT(1);
}

/***************************************/

#include "bfile.c"

/***************************************/

struct ioarray*
arr_alloc(size_t sz, NODEPTR e)
{
  struct ioarray *arr = mmalloc(sizeof(struct ioarray) + (sz-1) * sizeof(NODEPTR));
  size_t i;

  arr->next = array_root;
  array_root = arr;
  arr->marked = 0;
  arr->permanent = 0;
  arr->size = sz;
  for(i = 0; i < sz; i++)
    arr->array[i] = e;
  //PRINT("arr_alloc(%d, %p) = %p\n", (int)sz, e, arr);
  num_arr_alloc++;
  return arr;
}

struct ioarray*
arr_copy(struct ioarray *oarr)
{
  size_t sz = oarr->size;
  struct ioarray *arr = mmalloc(sizeof(struct ioarray) + (sz-1) * sizeof(NODEPTR));

  arr->next = array_root;
  array_root = arr;
  arr->marked = 0;
  arr->permanent = 0;
  arr->size = sz;
  memcpy(arr->array, oarr->array, sz * sizeof(NODEPTR));
  num_arr_alloc++;
  return arr;
}

/*****************************************************************************/

#if WANT_TICK
struct tick_entry {
  struct bytestring tick_name;
  counter_t tick_count;
} *tick_table = 0;
size_t tick_table_size;
size_t tick_index;

/* Allocate a new tick table entry and return the index. */
size_t
add_tick_table(struct bytestring name)
{
  if (!tick_table) {
    tick_table_size = 100;
    tick_table = mmalloc(tick_table_size * sizeof(struct tick_entry));
    tick_index = 0;
  }
  if (tick_index >= tick_table_size) {
    tick_table_size *= 2;
    tick_table = mrealloc(tick_table, tick_table_size * sizeof(struct tick_entry));
  }
  tick_table[tick_index].tick_name = name;
  tick_table[tick_index].tick_count = 0;
  return tick_index++;
}

/* Called with the tick index. */
static inline void
dotick(value_t i)
{
  tick_table[i].tick_count++;
}

void
dump_tick_table(FILE *f)
{
  if (!tick_table) {
    fprintf(f, "Tick table empty\n");
    return;
  }
  for (size_t i = 0; i < tick_index; i++) {
    counter_t n = tick_table[i].tick_count;
    if (n)
      fprintf(f, "%-60s %10"PRIcounter"\n", (char *)tick_table[i].tick_name.string, n);
  }
}
#endif

enum th_sched { mt_main, mt_resched, mt_raise };
/* The two enums below are known by the Haskell code.  Do not change order */
enum th_state { ts_runnable, ts_wait_mvar, ts_wait_time, ts_finished, ts_died };
enum mask_state { mask_unmasked, mask_interruptible, mask_uninterruptible };

/***************** HANDLER *****************/

struct handler {
  jmp_buf         hdl_buf;      /* env storage */
  struct handler *hdl_old;      /* old handler */
  NODEPTR         hdl_exn;      /* used temporarily to pass the exception value */
} *cur_handler = 0;

/***************** THREAD ******************/

struct mthread {
  enum th_state   mt_state;      /* thread state */
  enum mask_state mt_mask;       /* making state. */
  struct mthread *mt_next;       /* all threads linked together */
  struct mthread *mt_queue;      /* runq/waitq link */
  counter_t       mt_slice;      /* reduction steps until yielding */
  counter_t       mt_num_slices; /* number of slices so far */
  NODEPTR         mt_root;       /* root of the graph to reduce */
  struct mvar    *mt_exn;        /* possible thrown exception */
  NODEPTR         mt_mval;       /* filled after waiting for take/read */
  int             mt_mark;       /* marked as accessible */
  uvalue_t        mt_id;         /* thread number, thread 1 is the main thread */
#if defined(CLOCK_INIT)
  CLOCK_T         mt_at;         /* time to wake up when in threadDelay */
#endif
};
struct mthread  *all_threads = 0;   /* all threads */

struct mqueue {
  struct mthread *mq_head;
  struct mthread *mq_tail;
};
struct mqueue runq = { 0, 0 };;
struct mqueue timeq = { 0, 0 };

struct mvar {
  struct mvar    *mv_next;      /* all mvars linked together */
  NODEPTR         mv_data;      /* contents of the mvar, or NIL when empty */
  struct mqueue   mv_takeput;   /* queue of threads waiting for take or put, single wakeup */
  struct mqueue   mv_read;      /* queue of threads waiting for read, multiple wakeup */
  int             mv_mark;      /* marked as accessible */
};
struct mvar      *all_mvars = 0;   /* all mvars */

jmp_buf          sched;             /* jump here to yield */
counter_t        slice = 100000;    /* normal time slice;
                                     * on an M4 Mac this is about 0.3ms */
//REGISTER(counter_t glob_slice,r23);
REGISTER(int glob_slice,r23);

NODEPTR          the_exn;       /* Used to propagate the exception for longjmp(sched, mt_raise) */

/* The order of these must be kept in sync with Control.Exception.Internal.rtsExn */
enum rts_exn { exn_stackoverflow, exn_heapoverflow, exn_threadkilled, exn_userinterrupt, exn_dividebyzero };

NORETURN void raise_exn(NODEPTR exn);
struct mvar* new_mvar(void);
NODEPTR take_mvar(int try, struct mvar *mv);
NORETURN void die_exn(NODEPTR exn);
void thread_intr(struct mthread *mt);
int put_mvar(int try, struct mvar *mv, NODEPTR v);
NODEPTR mkInt(value_t i);
NODEPTR mkFlt(flt_t d);
NODEPTR mkPtr(void* p);
struct mthread* new_thread(NODEPTR root);
void gc(void);
void async_throwto(struct mthread*, NODEPTR);

#if WANT_STDIO
void pp(FILE*, NODEPTR);
#endif

/* Needed during reduction */
NODEPTR intTable[HIGH_INT - LOW_INT];
NODEPTR combK, combTrue, combUnit, combCons, combPair;
NODEPTR combCC, combZ, combIOBIND, combIORETURN, combIOTHEN, combB, combC, combBB;
NODEPTR combSETMASKINGSTATE;
NODEPTR combLT, combEQ, combGT;
NODEPTR combShowExn, combU, combK2, combK3;
NODEPTR combBININT1, combBININT2, combUNINT1;
NODEPTR combBINDBL1, combBINDBL2, combUNDBL1;
NODEPTR combBINBS1, combBINBS2;
NODEPTR comb_stdin, comb_stdout, comb_stderr;
NODEPTR combJust;
NODEPTR combTHROWTO;
NODEPTR combPairUnit;
NODEPTR combWorld;
NODEPTR combCATCHR;
#define combFalse combK
#define combNothing combK

#if WANT_ARGS
/* This single element array hold a list of the program arguments. */
struct ioarray *argarray;
#endif  /* WANT_ARGS */

int verbose = 0;
int gcbell = 0;


#if WANT_SIGINT
volatile int has_sigint = 0;
void
handle_sigint(int s)
{
  has_sigint = 1;
}
#endif

/* Check that there are k nodes available, if not then GC. */
static INLINE void
gc_check(size_t k)
{
  if (k < num_free)
    return;
#if WANT_STDIO
  if (verbose > 1)
    PRINT("gc_check: %d\n", (int)k);
#endif
  gc();
}

/* Add the thread to the tail of runq */
void
add_q_tail(struct mqueue *q, struct mthread *mt)
{
  if (!q->mq_head) {
    /* q is empty, so mt goes first */
    q->mq_head = mt;
  } else {
    /* link mt to the end of the runq */
    q->mq_tail->mt_queue = mt;
  }
  q->mq_tail = mt;               /* mt is now last */
  mt->mt_queue = 0;           /* mt is last, so no next */
}

void
add_runq_tail(struct mthread *mt)
{
  mt->mt_state = ts_runnable;
  add_q_tail(&runq, mt);
}

struct mthread*
remove_q_head(struct mqueue *q)
{
  struct mthread *mt = q->mq_head; /* front thread */
  if (!mt)
    return 0;
  q->mq_head = mt->mt_queue;       /* skip to next thread */
  if (!q->mq_head)
    q->mq_tail = 0;                /* q is now empty */
  return mt;
}

int
find_and_unlink(struct mqueue *mq, struct mthread *mt)
{
  struct mthread **mtp;
  
  for(mtp = &mq->mq_head; *mtp && *mtp != mt; mtp = &(*mtp)->mt_queue)
    ;
  if (!*mtp)
    return 0;                   /* not found */
  *mtp = mt->mt_queue;          /* unlink */
  if (*mtp)
    return 1;                   /* the unlinked thread was not the tail */
  if (mq->mq_head) {
    for (mt = mq->mq_head; mt->mt_queue; mt = mt->mt_queue)
      ;                         /* find the last element */
    mq->mq_tail = mt;
  } else {
    /* q is empty */
    mq->mq_tail = 0;
  }
  return 1;
}

/* This is a yucky hack */
int doing_rnf = 0;              /* REMOVE */
#if THREAD_DEBUG
const int thread_trace = 0;
#endif  /* THREAD_DEBUG */

/* clean up temporary globals to prepare for rescheduling */
void
cleanup(struct mthread *mt, enum th_state ts)
{
  /* We are going to reschedule, so clean up thread state:
   *  stack pointer
   *  error handlers
   */
#if THREAD_DEBUG
  if (thread_trace)
    printf("cleanup: %d state=%d\n", (int)mt->mt_id, ts);
#endif  /* THREAD_DEBUG */
  mt->mt_slice = stack_ptr;   /* we need stack_ptr reductions to just reach where we left off */
  mt->mt_state = ts;
  CLEARSTK();                 /* reset stack */
  doing_rnf = 0;
  /* free all error handlers */
  for (struct handler *h = cur_handler; h; ) {
    struct handler *n = h;
    h = h->hdl_old;
    free(n);
  }
  cur_handler = 0;
}

/* reschedule, does not return */
NORETURN void
resched(struct mthread *mt, enum th_state ts)
{
  cleanup(mt, ts);
  longjmp(sched, mt_resched);
}

#if THREAD_DEBUG
void
dump_q(const char *s, struct mqueue q)
{
  printf("%s=[", s);
  for(struct mthread *mt = q.mq_head; mt; mt = mt->mt_queue) {
    printf("%d ", (int)mt->mt_id);
  }
  printf("]\n");
}
#endif  /* THREAD_DEBUG */

/* Check if its time to wake up some threads waiting for a time. */
void
check_timeq(void)
{
#if defined(CLOCK_INIT)
  CLOCK_T now = CLOCK_GET();
  while (timeq.mq_head && timeq.mq_head->mt_at <= now) {
    struct mthread *mt = remove_q_head(&timeq);
    add_runq_tail(mt);
    mt->mt_at = -1;             /* indicate that the delay has expired */
#if THREAD_DEBUG
    if (thread_trace)
      printf("check_timeq: %d done\n", (int)mt->mt_id);
#endif  /* THREAD_DEBUG */
  }
#endif
}

void
throwto(struct mthread *mt, NODEPTR exn)
{
#if THREAD_DEBUG
  if (thread_trace) {
    printf("throwto: id=%d\n", (int)mt->mt_id);
  }
#endif  /* THREAD_DEBUG */
  thread_intr(mt);
  if (mt->mt_state != ts_died && mt->mt_state != ts_finished) {
#if THREAD_DEBUG
    if (thread_trace) {
      printf("throwto: id=%d put_mvar exn\n", (int)mt->mt_id);
    }
#endif  /* THREAD_DEBUG */
    (void)put_mvar(0, mt->mt_exn, exn); /* never returns if it blocks */
  }
}

void
check_thrown(void)
{
  if (runq.mq_head->mt_exn->mv_data == NIL)
    return;            /* no thrown exception */
  if (runq.mq_head->mt_mask != mask_unmasked)
    return;            /* interrupts are masked, so don't throw */
  /* the current thread has an async exception */
#if THREAD_DEBUG
  if (thread_trace)
    printf("check_thrown: exn for %d\n", (int)runq.mq_head->mt_id);
#endif  /* THREAD_DEBUG */
  NODEPTR exn = take_mvar(0, runq.mq_head->mt_exn); /* get the exception */
  raise_exn(exn);
}

void
check_sigint(void)
{
#if WANT_SIGINT
  if (has_sigint) {
    /* We have a signal, so send an async exception  to the main thread */
    has_sigint = 0;
    for(struct mthread *mt= all_threads; mt; mt = mt->mt_next) {
      if (mt->mt_id == MAIN_THREAD) {
#if THREAD_DEBUG
        if (thread_trace)
          printf("sending signal to main\n");
#endif  /* THREAD_DEBUG */
        async_throwto(mt, mkInt(exn_userinterrupt));
        break;
      }
    }
  }
#endif
}

/* Used to detect calls to error while we are already in a call to error. */
int in_raise = 0;

/* Inlining makes very little difference */
/*static INLINE*/ void
yield(void)
{
  if (in_raise)                 /* don't context switch when we are dying */
    return;
  //printf("yield stk=%d\n", (int)stack_ptr);
  //pp(stdout, runq.mt_root);
  COUNT(num_yield);
  runq.mq_head->mt_num_slices++;
  // XXX should check mt_thrown here
  
  if (timeq.mq_head)
    check_timeq();
  check_thrown();
  check_sigint();
  // printf("yield %p %d\n", runq, (int)stack_ptr);
  /* if there is nothing after in the runq then there is no need to reschedule */
  if (!runq.mq_head->mt_queue) {
#if THREAD_DEBUG
    if (thread_trace) {
      printf("yield: %d no other threads\n", (int)runq.mq_head->mt_id);
      dump_q("runq", runq);
    }
#endif  /* THREAD_DEBUG */
    glob_slice = slice;
    num_reductions += glob_slice-1;
    return;
  }

  /* Unlink from runq */
  struct mthread *mt = remove_q_head(&runq);
  /* link into back of runq */
  add_runq_tail(mt);
#if THREAD_DEBUG
  if (thread_trace) {
    printf("yield: resched %d\n", (int)mt->mt_id);
    dump_q("runq", runq);
  }
#endif  /* THREAD_DEBUG */
  resched(mt, ts_runnable);
}

struct mthread*
new_thread(NODEPTR root)
{
  struct mthread *mt = mmalloc(sizeof(struct mthread));

#if THREAD_DEBUG
  if (thread_trace) {
    printf("new_thread: mt=%p root=%p\n", mt, root);
  }
#endif  /* THREAD_DEBUG */
  mt->mt_mask = mask_unmasked;
  mt->mt_root = root;
  mt->mt_exn = new_mvar();
  mt->mt_mval = NIL;
  mt->mt_slice = 0;
  mt->mt_mark = 0;
  mt->mt_num_slices = 0;
  mt->mt_id = num_thread_create++;
#if defined(CLOCK_INIT)
  mt->mt_at = 0;                /* delay has not expired */
#endif

  /* add to all_threads */
  mt->mt_next = all_threads;
  all_threads = mt;

  /* add to tail of runq */
  add_runq_tail(mt);            /* sets runnable */
#if THREAD_DEBUG
  if (thread_trace) {
    printf("new_thread: add %d to runq tail\n", (int)mt->mt_id);
    dump_q("runq", runq);
  }
#endif  /* THREAD_DEBUG */
  return mt;
}

struct mvar*
new_mvar(void)
{
  COUNT(num_mvar_alloc);
  struct mvar *mv = mmalloc(sizeof(struct mvar));

  mv->mv_data = NIL;
  mv->mv_takeput.mq_head = 0;
  mv->mv_takeput.mq_tail = 0;
  mv->mv_read.mq_head = 0;
  mv->mv_read.mq_tail = 0;

  /* add to all_mvars */
  mv->mv_next = all_mvars;
  mv->mv_mark = 0;
  all_mvars = mv;
  
#if THREAD_DEBUG
  if (thread_trace)
    printf("new_mvar: mvar=%p\n", mv);
#endif  /* THREAD_DEBUG */
  return mv;
}

NODEPTR
take_mvar(int try, struct mvar *mv)
{
#if THREAD_DEBUG
  if (thread_trace) {
    printf("take_mvar: mvar=%p\n", mv);
    dump_q("takeput", mv->mv_takeput);
  }
#endif  /* THREAD_DEBUG */
  NODEPTR n;
  if ((n = runq.mq_head->mt_mval) != NIL) {
#if THREAD_DEBUG
    if (thread_trace)
      printf("take_mvar: mvar=%p got data %d\n", mv, (int)runq.mq_head->mt_id);
#endif  /* THREAD_DEBUG */
    /* We have after waking up */
    runq.mq_head->mt_mval = NIL;
    return n;                   /* returned the stashed data */
  }
  if ((n = mv->mv_data) != NIL) {
#if THREAD_DEBUG
    if (thread_trace)
      printf("take_mvar: mvar=%p full\n", mv);
#endif  /* THREAD_DEBUG */
    /* mvar is full */
    mv->mv_data = NIL;           /* now empty */
    /* move all threads waiting to put to the runq */
    for (struct mthread *mt = mv->mv_takeput.mq_head; mt; ) {
#if THREAD_DEBUG
      if (thread_trace) {
        printf("take_mvar: mvar=%p wake %d\n", mv, (int)mt->mt_id);
      }
#endif  /* THREAD_DEBUG */
      struct mthread *nt = mt->mt_queue;
      add_runq_tail(mt);
#if THREAD_DEBUG
      if (thread_trace) {
        dump_q("runq", runq);
      }
#endif  /* THREAD_DEBUG */
      mt = nt;
    }
#if THREAD_DEBUG
    if (thread_trace) {
      printf("take_mvar: mvar=%p return %p\n", mv, n);
    }
#endif  /* THREAD_DEBUG */
    return n;                   /* return the data */
  } else {
#if THREAD_DEBUG
    if (thread_trace)
      printf("take_mvar: mvar=%p empty\n", mv);
#endif  /* THREAD_DEBUG */
    /* mvar is empty */
    if (try)
      return NIL;
    struct mthread *mt = remove_q_head(&runq);
    add_q_tail(&mv->mv_takeput, mt);
#if THREAD_DEBUG
    if (thread_trace) {
      printf("take_mvar: mvar=%p suspend %d\n", mv, (int)mt->mt_id);
      dump_q("runq", runq);
      dump_q("takeput", mv->mv_takeput);
    }
#endif  /* THREAD_DEBUG */
    /* Unlink from runq */
    resched(mt, ts_wait_mvar);    /* never returns */
  }
}

NODEPTR
read_mvar(int try, struct mvar *mv)
{
  NODEPTR n;
  if ((n = runq.mq_head->mt_mval) != NIL) {
    /* We have after waking up */
    runq.mq_head->mt_mval = NIL;
    return n;                   /* returned the stashed data */
  }
  if ((n = mv->mv_data) != NIL) {
    /* mvar is full */
    return n;                   /* return the data */
  } else {
    /* mvar is empty */
    if (try)
      return NIL;
#if THREAD_DEBUG
    if (thread_trace) {
      printf("read_mvar: suspend %d\n", (int)runq.mq_head->mt_id);
      dump_q("runq", runq);
    }
#endif  /* THREAD_DEBUG */
    struct mthread *mt = remove_q_head(&runq);
    add_q_tail(&mv->mv_read, mt);
    resched(mt, ts_wait_mvar);                /* never returns */
  }
}

int
put_mvar(int try, struct mvar *mv, NODEPTR v)
{
#if THREAD_DEBUG
  if (thread_trace) {
    printf("put_mvar: mvar=%p\n", mv);
    dump_q("takeput", mv->mv_takeput);
    dump_q("read", mv->mv_read);
  }
#endif  /* THREAD_DEBUG */
  if (mv->mv_data != NIL) {
#if THREAD_DEBUG
    if (thread_trace)
      printf("put_mvar: mvar=%p full\n", mv);
#endif  /* THREAD_DEBUG */
    /* mvar is full */
    if (try)
      return 0;
    struct mthread *mt = remove_q_head(&runq);
    add_q_tail(&mv->mv_takeput, mt); /* put on mvar queue */
#if THREAD_DEBUG
    if (thread_trace) {
      printf("put_mvar: suspend %d\n", (int)mt->mt_id);
      dump_q("runq", runq);
      dump_q("takeput", mv->mv_takeput);
    }
#endif  /* THREAD_DEBUG */
    resched(mt, ts_wait_mvar);                  /* never returns */
  } else {
#if THREAD_DEBUG
    if (thread_trace)
      printf("put_mvar: mvar=%p empty\n", mv);
#endif  /* THREAD_DEBUG */
    /* mvar is empty */
    if (mv->mv_takeput.mq_head || mv->mv_read.mq_head) {
      /* one or more threads are waiting */
      struct mthread *mt;
      if (mv->mv_takeput.mq_head) {
        /* wake up one 'take' */
        mt = remove_q_head(&mv->mv_takeput);
#if THREAD_DEBUG
        if (thread_trace)
          printf("put_mvar: wake-1 %d\n", (int)mt->mt_id);
#endif  /* THREAD_DEBUG */
        add_runq_tail(mt);             /* and schedule for execution later */
        mt->mt_mval = v;
      }
      for (mt = mv->mv_read.mq_head; mt; ) { /* XXX use q primitives */
#if THREAD_DEBUG
        if (thread_trace)
          printf("put_mvar: wake-N %d\n", (int)mt->mt_id);
#endif  /* THREAD_DEBUG */
        mt->mt_mval = v;               /* value for restarted read */
        mt = mt->mt_queue;             /* next waiter */
        add_runq_tail(mt);             /* and schedule for execution later */
      }
#if THREAD_DEBUG
      if (thread_trace)
        dump_q("runq", runq);
#endif  /* THREAD_DEBUG */
      /* return to caller */
    } else {
#if THREAD_DEBUG
      if (thread_trace) {
        printf("put_mvar: mvar=%p no waiters\n", mv);
      }
#endif  /* THREAD_DEBUG */
      /* no threads waiting, so store the value */
      mv->mv_data = v;
      /* return to caller */
    }
  }
  return 1;
}

NORETURN void
thread_delay(uvalue_t usecs)
{
#if !defined(CLOCK_INIT)
  ERR("thread_delay: no clock");
#else
  /* XXX should check if there is already a throw exn */
  struct mthread *mt = remove_q_head(&runq);
  mt->mt_at = CLOCK_GET() + usecs; /* wakeup time */
#if THREAD_DEBUG
  if (thread_trace)
    printf("thread_delay: id=%d usecs=%ld\n", (int)mt->mt_id, (long)usecs);
#endif  /* THREAD_DEBUG */
  /* insert in delayq which is kept sorted in time order */
  struct mthread **tq;
  for (tq = &timeq.mq_head; *tq; tq = &(*tq)->mt_queue) {
    if (mt->mt_at <= (*tq)->mt_at)
      break;
  }
  mt->mt_queue = *tq;           /* forward link */
  *tq = mt;                     /* and put mt in place */
  if (!mt->mt_queue)            /* no forward link */
    timeq.mq_tail = mt;
  resched(mt, ts_wait_time);
#endif  
}

/* Pause execution if something might still happen */
void
pause_exec(void)
{
#if defined(CLOCK_INIT)
  if (timeq.mq_head) {
    struct mthread *mt;
    while (!runq.mq_head && (mt = timeq.mq_head)) {
      /* We are waiting for a delay to expire, so sleep a while */
      CLOCK_T dly = mt->mt_at - CLOCK_GET();
      if (dly > 0) {
        /* usleep() can be unreliable, so sleep shorter than the delay */
        dly /= 4;
        if (dly < 50) dly = 50;
        CLOCK_SLEEP((useconds_t)dly);
      }
      check_timeq();
    }
  } else {
    ERR("deadlock");            /* XXX throw async to main thread */
  }
#else  /* CLOCK_INIT */
  ERR("no clock");
#endif  /* CLOCK_INIT */
}

/* Interrupt a sleeping thread in a throwTo/threadDelay */
void
thread_intr(struct mthread *mt)
{
#if THREAD_DEBUG
  if (thread_trace)
    printf("thread_intr: id=%d state=%d\n", (int)mt->mt_id, mt->mt_state);
#endif  /* THREAD_DEBUG */
  switch(mt->mt_state) {
  case ts_runnable:
    break;                      /* already on runq */
  case ts_wait_mvar:
    if (mt->mt_mask == mask_uninterruptible) /* uninterruptible */
      break;
    /* we don't know which mvar we are waiting on, so look at all of them */
    /* XXX should add a pointer in mthread to the mvar */
    for (struct mvar *mv = all_mvars; mv; mv = mv->mv_next) {
      if (find_and_unlink(&mv->mv_takeput, mt))
          goto found;
      if (find_and_unlink(&mv->mv_read, mt))
          goto found;
    }
    ERR("thread_intr: mvar");
  found:
#if defined(CLOCK_INIT)
    mt->mt_at = -1;             /* don't wait again */
#endif
    add_runq_tail(mt);
    break;
  case ts_wait_time:
#if THREAD_DEBUG
    if (thread_trace) {
      printf("thread_intr: ts_wait_time mask=%d\n", (int)mt->mt_mask);
    }
#endif  /* THREAD_DEBUG */
    if (mt->mt_mask == mask_uninterruptible) /* uninterruptible */
      break;
    /* find thread in timeq */
    if (!find_and_unlink(&timeq, mt))
      ERR("thread_intr: timeq");
    /* XXX should adjust mq_tail */
    add_runq_tail(mt);
    break;
  case ts_finished:
  case ts_died:
    (void)take_mvar(0, mt->mt_exn); /* ignore exception */
    break;
  default:
    ERR("thread_intr");
  }
#if THREAD_DEBUG
  if (thread_trace) {
    printf("thread_intr: done\n");
    dump_q("runq", runq);
  }
#endif  /* THREAD_DEBUG */
}

NORETURN void
raise_exn(NODEPTR exn)
{
  if (cur_handler) {
    /* Pass the exception to the handler */
    cur_handler->hdl_exn = exn;
    longjmp(cur_handler->hdl_buf, 1);
  } else {
    /* No exception handler, jump to the scheduler */
    the_exn = exn;
    longjmp(sched, mt_raise);
  }
}

NORETURN void
raise_rts(enum rts_exn exn) {
  raise_exn(mkInt(exn));
}

/***************** GC ******************/

/* Set FREE bit to 0 */
static INLINE void mark_used(NODEPTR n)
{
  heapoffs_t i = LABEL(n);
  if (i < heap_start)
    return;
#if SANITY
  if (i >= free_map_nwords * BITS_PER_WORD) ERR("mark_used");
#endif
  free_map[i / BITS_PER_WORD] &= ~(1ULL << (i % BITS_PER_WORD));
}

/* Set FREE bit to 1, used to undo marking in GC */
static INLINE void mark_unused(NODEPTR n)
{
  heapoffs_t i = LABEL(n);
#if SANITY
  if (i < heap_start)
    ERR("Unmarking invalid heap address.");
  if (i >= free_map_nwords * BITS_PER_WORD) ERR("mark_used");
#endif
  free_map[i / BITS_PER_WORD] |= 1ULL << (i % BITS_PER_WORD);
}

/* Test if FREE bit is 0 */
static INLINE int is_marked_used(NODEPTR n)
{
  heapoffs_t i = LABEL(n);
  if (i < heap_start)
    return 1;
#if SANITY
  if (i >= free_map_nwords * BITS_PER_WORD)
    ERR("is_marked_used");
#endif
  return (free_map[i / BITS_PER_WORD] & (1ULL << (i % BITS_PER_WORD))) == 0;
}

static INLINE void mark_all_free(void)
{
  memset(free_map, ~0, free_map_nwords * sizeof(bits_t));
  next_scan_index = heap_start;
}

static INLINE NODEPTR
alloc_node(enum node_tag t)
{
  heapoffs_t i = next_scan_index / BITS_PER_WORD;
  int k;                        /* will contain bit pos + 1 */
  heapoffs_t pos;
  NODEPTR n;
  heapoffs_t word;

  /* This can happen if we run out of memory when parsing. */
  if (num_free <= 0)
    ERR("alloc_node");

  for(;;) {
    word = free_map[i];
    if (word)
      break;
    i++;
#if SANITY
    if (i >= free_map_nwords) {
#if 0
      fprintf(stderr, "wordsize=%u, num_free=%u next_scan_index=%u i=%u free_map_nwords=%u\n", (uint)BITS_PER_WORD,
              (uint)num_free, (uint)next_scan_index, (uint)i, (uint)free_map_nwords);
#endif
      ERR("alloc_node: free_map");
    }
#endif
  }
  k = FFS(word);
  pos = i * BITS_PER_WORD + k - 1; /* first free node */
  n = HEAPREF(pos);
  // mark_used(n); // equivalent to:
  free_map[i] = word & (word-1);
  next_scan_index = pos;

  SETTAG(n, t);
  COUNT(num_alloc);
  num_free--;
  return n;
}

static INLINE NODEPTR
new_ap(NODEPTR f, NODEPTR a)
{
  NODEPTR n = alloc_node(T_AP);
  FUN(n) = f;
  ARG(n) = a;
  return n;
}

NODEPTR evali(NODEPTR n);

void
start_exec(NODEPTR root)
{
  struct mthread *mt;

  new_thread(new_ap(root, combWorld)); /* main thread */

  switch(setjmp(sched)) {
  case mt_main:
    break;
  case mt_resched:
    COUNT(num_resched);
    break;
  case mt_raise:
    /* We have an uncaught exception.
     * If it's the main thread, this kills the program.
     * Otherwise, it just kills the thread.
     */
    mt = remove_q_head(&runq);
    if (mt->mt_id == MAIN_THREAD) {
      die_exn(the_exn);
    } else {
#if THREAD_DEBUG
      if (thread_trace) {
        printf("start_exec: mt=%p id=%d died from exn\n", mt, (int)mt->mt_id);
      }
#endif  /* THREAD_DEBUG */
      mt->mt_state = ts_died;
      mt->mt_root = NIL;
    }
  }
#if THREAD_DEBUG
  if (thread_trace) {
    printf("start_exec:\n");
    dump_q("runq", runq);
  }
#endif  /* THREAD_DEBUG */
  for(;;) {
    if (!runq.mq_head)
      pause_exec();
    mt = runq.mq_head;          /* front thread */
    if (!mt)                    /* this should never happen */
      ERR("no threads");

    glob_slice = mt->mt_slice + slice;
#if THREAD_DEBUG
    if (thread_trace)
      printf("start_exec: start %d, slice=%d\n", (int)mt->mt_id, (int)glob_slice);
#endif  /* THREAD_DEBUG */
    num_reductions += glob_slice-1;
    (void)evali(mt->mt_root);         /* run it */
    num_reductions -= glob_slice;
    /* when evali() returns the thread is done */
    (void)remove_q_head(&runq);                      /* remove front thread */

#if THREAD_DEBUG
    if (thread_trace) {
      printf("start_exec: mt=%p id=%d finished\n", mt, (int)mt->mt_id);
    }
#endif  /* THREAD_DEBUG */
    mt->mt_state = ts_finished;
    mt->mt_root = NIL;
    /* XXX mt_mval, mt_thrown */

    if (mt->mt_id == MAIN_THREAD)
      return;                   /* when the main thread dies it's all over */
  }
}

/* One node of each kind for primitives, these are never GCd. */
/* We use linear search in this, because almost all lookups
 * are among the combinators.
 */
struct {
  const char *name;
  const enum node_tag tag;
  const enum node_tag flipped;        /* What should (C op) reduce to? defaults to T_FREE */
  NODEPTR node;
} primops[] = {
  /* combinators */
  /* sorted by frequency in a typical program */
  { "B", T_B },
  { "O", T_O },
  { "K", T_K, T_A },
  { "C'", T_CC },
  { "C", T_C },
  { "A", T_A, T_K },
  { "S'", T_SS },
  { "P", T_P },
  { "R", T_R },
  { "I", T_I },
  { "S", T_S },
  { "U", T_U },
  { "Y", T_Y },
  { "B'", T_BB },
  { "Z", T_Z },
  /*  { "J", T_J },*/
  { "K2", T_K2 },
  { "K3", T_K3 },
  { "K4", T_K4 },
  { "C'B", T_CCB },
/* primops */
  { "+", T_ADD, T_ADD },
  { "-", T_SUB, T_SUBR },
  { "*", T_MUL, T_MUL },
  { "quot", T_QUOT },
  { "rem", T_REM },
  { "uquot", T_UQUOT },
  { "urem", T_UREM },
  { "subtract", T_SUBR, T_SUB },
  { "neg", T_NEG },
  { "and", T_AND, T_AND },
  { "or", T_OR, T_OR },
  { "xor", T_XOR, T_XOR },
  { "inv", T_INV },
  { "shl", T_SHL },
  { "shr", T_SHR },
  { "ashr", T_ASHR },
  { "popcount", T_POPCOUNT },
  { "clz", T_CLZ },
  { "ctz", T_CTZ },
#if WANT_FLOAT
  { "f+" , T_FADD, T_FADD},
  { "f-" , T_FSUB },
  { "f*" , T_FMUL, T_FMUL},
  { "f/", T_FDIV},
  { "fneg", T_FNEG},
  { "itof", T_ITOF},
  { "f==", T_FEQ, T_FEQ},
  { "f/=", T_FNE, T_FNE},
  { "f<", T_FLT, T_FGT},
  { "f<=", T_FLE, T_FGE},
  { "f>", T_FGT, T_FLT},
  { "f>=", T_FGE, T_FLE},
  { "fshow", T_FSHOW},
  { "fread", T_FREAD},
#endif  /* WANT_FLOAT */

  { "bs++", T_BSAPPEND },
  { "bs++.", T_BSAPPENDDOT },
  { "bs==", T_BSEQ, T_BSEQ },
  { "bs/=", T_BSNE, T_BSNE },
  { "bs<", T_BSLT, T_BSGT },
  { "bs<=", T_BSLE, T_BSGE  },
  { "bs>", T_BSGT, T_BSLT },
  { "bs>=", T_BSGE, T_BSLE  },
  { "bscmp", T_BSCMP },
  { "bspack", T_BSPACK },
  { "bsunpack", T_BSUNPACK },
  { "bsreplicate", T_BSREPLICATE },
  { "bslength", T_BSLENGTH },
  { "bssubstr", T_BSSUBSTR },
  { "bsindex", T_BSINDEX },

  { "ord", T_I },
  { "chr", T_I },
  { "==", T_EQ, T_EQ },
  { "/=", T_NE, T_NE },
  { "<", T_LT, T_GT },
  { "u<", T_ULT, T_UGT },
  { "u<=", T_ULE, T_UGE },
  { "u>", T_UGT, T_ULT },
  { "u>=", T_UGE, T_ULE },
  { "<=", T_LE, T_GE },
  { ">", T_GT, T_LT },
  { ">=", T_GE, T_LE },
  { "fp+", T_FPADD },
  { "fp2p", T_FP2P },
  { "fpnew", T_FPNEW },
  { "fpfin", T_FPFIN },
  //  { "fpstr", T_FPSTR },
  { "fp2bs", T_FP2BS },
  { "bs2fp", T_BS2FP },
  { "seq", T_SEQ },
  { "equal", T_EQUAL, T_EQUAL },
  { "sequal", T_EQUAL, T_EQUAL },
  { "compare", T_COMPARE },
  { "scmp", T_COMPARE },
  { "icmp", T_ICMP },
  { "ucmp", T_UCMP },
  { "rnf", T_RNF },
  { "fromUTF8", T_BSFROMUTF8 },
  { "toUTF8", T_BSTOUTF8 },
  { "headUTF8", T_BSHEADUTF8 },
  { "tailUTF8", T_BSTAILUTF8 },
  /* IO primops */
  { "IO.>>=", T_IO_BIND },
  { "IO.>>", T_IO_THEN },
  { "IO.return", T_IO_RETURN },
  { "IO.serialize", T_IO_SERIALIZE },
  { "IO.print", T_IO_PRINT },
  { "IO.deserialize", T_IO_DESERIALIZE },
  { "IO.stdin", T_IO_STDIN },
  { "IO.stdout", T_IO_STDOUT },
  { "IO.stderr", T_IO_STDERR },
  { "IO.getArgRef", T_IO_GETARGREF },
  { "IO.performIO", T_IO_PERFORMIO },
  { "IO.gc", T_IO_GC },
  { "IO.stats", T_IO_STATS },
  { "IO.pp", T_IO_PP },
  { "raise", T_RAISE },
  { "catch", T_CATCH },
  { "catchr", T_CATCHR },
  { "A.alloc", T_ARR_ALLOC },
  { "A.copy", T_ARR_COPY },
  { "A.size", T_ARR_SIZE },
  { "A.read", T_ARR_READ },
  { "A.write", T_ARR_WRITE },
  { "A.==", T_ARR_EQ },
  { "dynsym", T_DYNSYM },
  { "IO.fork", T_IO_FORK },
  { "IO.thid", T_IO_THID },
  { "thnum", T_THNUM },
  { "IO.throwto", T_IO_THROWTO },
  { "IO.yield", T_IO_YIELD },
  { "IO.newmvar", T_IO_NEWMVAR },
  { "IO.takemvar", T_IO_TAKEMVAR },
  { "IO.putmvar", T_IO_PUTMVAR },
  { "IO.readmvar", T_IO_READMVAR },
  { "IO.trytakemvar", T_IO_TRYTAKEMVAR },
  { "IO.tryputmvar", T_IO_TRYPUTMVAR },
  { "IO.tryreadmvar", T_IO_TRYREADMVAR },
  { "IO.threaddelay", T_IO_THREADDELAY },
  { "IO.threadstatus", T_IO_THREADSTATUS },
  { "IO.getmaskingstate", T_IO_GETMASKINGSTATE },
  { "IO.setmaskingstate", T_IO_SETMASKINGSTATE },
  { "newCAStringLen", T_NEWCASTRINGLEN },
  { "packCString", T_PACKCSTRING },
  { "packCStringLen", T_PACKCSTRINGLEN },
  { "toPtr", T_TOPTR },
  { "toInt", T_TOINT },
  { "toDbl", T_TODBL },
  { "toFunPtr", T_TOFUNPTR },
  { "IO.ccall", T_IO_CCALL },
  { "isint", T_ISINT },
  { "binint2", T_BININT2 },
  { "binint1", T_BININT1 },
  { "bindbl2", T_BINDBL2 },
  { "bindbl1", T_BINDBL1 },
  { "binbs2", T_BINBS2 },
  { "binbs1", T_BINBS1 },
  { "unint1", T_UNINT1 },
  { "undbl1", T_UNDBL1 },
};

#if GCRED
enum node_tag flip_ops[T_LAST_TAG+1];
#endif

#if WANT_STDIO
/* Create a dummy foreign pointer for the standard stdio handles. */
/* These handles are never gc():d. */
void
mk_std(NODEPTR n, FILE *f)
{
  struct final *fin = mcalloc(1, sizeof(struct final));
  struct forptr *fp = mcalloc(1, sizeof(struct forptr));
  BFILE *bf = add_utf8(add_FILE(f));
  SETTAG(n, T_FORPTR);
  FORPTR(n) = fp;
  fin->arg = bf;
  fin->back = fp;
  fp->payload.string = bf;
  fp->finalizer = fin;
}
#endif

void
init_nodes(void)
{
  enum node_tag t;
  size_t j;
  NODEPTR n;

  ALLOC_HEAP(heap_size);
  free_map_nwords = (heap_size + BITS_PER_WORD - 1) / BITS_PER_WORD; /* bytes needed for free map */
  free_map = mmalloc(free_map_nwords * sizeof(bits_t));

  /* Set up permanent nodes */
  heap_start = 0;
  for(t = T_FREE; t <= T_LAST_TAG; t++) {
    NODEPTR n = HEAPREF(heap_start++);
    SETTAG(n, t);
    switch (t) {
    case T_K: combK = n; break;
    case T_A: combTrue = n; break;
    case T_I: combUnit = n; break;
    case T_O: combCons = n; break;
    case T_P: combPair = n; break;
    case T_CC: combCC = n; break;
    case T_BB: combBB = n; break;
    case T_B: combB = n; break;
    case T_C: combC = n; break;
    case T_Z: combZ = n; break;
    case T_U: combU = n; break;
    case T_K2: combK2 = n; break;
    case T_K3: combK3 = n; break;
    case T_IO_BIND: combIOBIND = n; break;
    case T_IO_THEN: combIOTHEN = n; break;
    case T_IO_RETURN: combIORETURN = n; break;
    case T_IO_SETMASKINGSTATE: combSETMASKINGSTATE = n; break;
    case T_BININT1: combBININT1 = n; break;
    case T_BININT2: combBININT2 = n; break;
    case T_UNINT1: combUNINT1 = n; break;
    case T_BINDBL1: combBINDBL1 = n; break;
    case T_BINDBL2: combBINDBL2 = n; break;
    case T_UNDBL1: combUNDBL1 = n; break;
    case T_BINBS1: combBINBS1 = n; break;
    case T_BINBS2: combBINBS2 = n; break;
    case T_IO_THROWTO: combTHROWTO = n; break;
    case T_CATCHR: combCATCHR = n; break;
#if WANT_STDIO
    case T_IO_STDIN:  comb_stdin  = n; mk_std(n, stdin);  break;
    case T_IO_STDOUT: comb_stdout = n; mk_std(n, stdout); break;
    case T_IO_STDERR: comb_stderr = n; mk_std(n, stderr); break;
#endif
    default:
      break;
    }
    for (j = sizeof primops / sizeof primops[0]; j-- > 0; ) {
      if (primops[j].tag == t) {
        primops[j].node = n;
      }
      tag_names[primops[j].tag] = primops[j].name;
    }
  }

#if GCRED
  for (j = 0; j < sizeof primops / sizeof primops[0]; j++) {
    flip_ops[primops[j].tag] = primops[j].flipped;
  }
#endif

  /* The representation of the constructors of
   *  data Ordering = LT | EQ | GT
   * do not have single constructors.
   * But we can make compound one, since they are irreducible.
   */
#define NEWAP(c, f, a) do { n = HEAPREF(heap_start++); SETTAG(n, T_AP); FUN(n) = (f); ARG(n) = (a); (c) = n;} while(0)
#define MKINT(c, i) do { n = HEAPREF(heap_start++); SETTAG(n, T_INT); SETVALUE(n, i); (c) = n; } while(0)
  NEWAP(combLT, combZ,     combFalse);  /* Z K */
  NEWAP(combEQ, combFalse, combFalse);  /* K K */
  NEWAP(combGT, combFalse, combTrue);   /* K A */
  {
    /* The displaySomeException compiles to (U (U (K2 A))) */
    NODEPTR x;
    NEWAP(x, combK2, combTrue);        /* (K2 A) */
    NEWAP(x, combU, x);                /* (U (K2 A)) */
    NEWAP(combShowExn, combU, x);      /* (U (U (K2 A))) */
  }
  NEWAP(combJust, combZ, combU);       /* (Z U) */
  MKINT(combWorld, 99999);
  NEWAP(combPairUnit, combPair, combUnit);
#undef NEWAP

#if INTTABLE
  /* Allocate permanent Int nodes */
  for (int i = LOW_INT; i < HIGH_INT; i++) {
    NODEPTR n = HEAPREF(heap_start++);
    intTable[i - LOW_INT] = n;
    SETTAG(n, T_INT);
    SETVALUE(n, i);
  }
#endif

  /* Round up heap_start to the next bitword boundary to avoid the permanent nodes. */
  heap_start = (heap_start + BITS_PER_WORD - 1) / BITS_PER_WORD * BITS_PER_WORD;

  mark_all_free();

  num_free = heap_size - heap_start;
}

#if GCRED
counter_t red_a, red_k, red_i, red_int, red_flip, red_bi, red_bxi, red_ccbi, red_cc, red_cci, red_ccbbcp;
#endif
counter_t red_bb, red_k4, red_k3, red_k2, red_ccb, red_z, red_r;

//counter_t mark_depth;
//counter_t max_mark_depth = 0;

void mark(NODEPTR *np);
void mark_mvar(struct mvar *mv);

/* Throwing, e.g., a UserInterrupt exception to the main thread
 * it can happen from any thread (the one that happens to poll).
 * Throwing an exception can block, so we can't throw it from
 * the current thread.  Instead, we spawn a new thread, whose
 * only job it is to throw the exception.
 */
void
async_throwto(struct mthread *mt, NODEPTR exn)
{
  GCCHECK(4);
  NODEPTR thid = alloc_node(T_THID);
  THR(thid) = mt;
  NODEPTR root = new_ap(new_ap(new_ap(combTHROWTO, thid), exn), combWorld);
  (void)new_thread(root);       /* spawn and put on runq */
}

void
mark_thread(struct mthread *mt)
{
  if (mt->mt_mark)
    return;                     /* already marked */
  mt->mt_mark = 1;
  if (mt->mt_root != NIL)
    mark(&mt->mt_root);
  mark_mvar(mt->mt_exn);         
  if (mt->mt_mval != NIL)
    mark(&mt->mt_mval);
}

void
mark_mvar(struct mvar *mv)
{
  if (mv->mv_mark)
    return;
  mv->mv_mark = 1;
  if (mv->mv_data != NIL)
    mark(&mv->mv_data);
  for (struct mthread *mt = mv->mv_takeput.mq_head; mt; mt = mt->mt_next)
    mark_thread(mt);
  for (struct mthread *mt = mv->mv_read.mq_head; mt; mt = mt->mt_next)
    mark_thread(mt);
}
  
/* Follow indirections */
static INLINE NODEPTR
indir(NODEPTR *np)
{
  NODEPTR n = *np;
  while (GETTAG(n) == T_IND)
    n = GETINDIR(n);
  *np = n;
  return n;
}

/* Mark all used nodes reachable from *np, updating *np. */
void
mark(NODEPTR *np)
{
  stackptr_t stk = stack_ptr;
  NODEPTR n;
  NODEPTR *to_push = 0;         /* silence warning by initializing */
#if GCRED
  value_t val;
#endif
  enum node_tag tag;

  //  mark_depth++;
  //  if (mark_depth % 10000 == 0)
  //    PRINT("mark depth %"PRIcounter"\n", mark_depth);
  top:
  n = *np;
  tag = GETTAG(n);
  if (tag == T_IND) {
#if SANITY
    int loop = 0;
    /* Skip indirections, and redirect start pointer */
    while ((tag = GETTAG(n)) == T_IND) {
      //      PRINT("*"); fflush(stdout);
      n = GETINDIR(n);
      if (loop++ > 10000000) {
        //PRINT("%p %p %p\n", n, GETINDIR(n), GETINDIR(GETINDIR(n)));
        ERR("IND loop");
      }
    }
    //    if (loop)
    //      PRINT("\n");
#else  /* SANITY */
    while ((tag = GETTAG(n)) == T_IND) {
      n = GETINDIR(n);
    }
#endif  /* SANITY */
    *np = n;
  }
  if (n < cells || n > cells + heap_size)
    ERR("bad n");
  if (is_marked_used(n)) {
    goto fin;
  }
  num_marked++;
  mark_used(n);
  switch (tag) {
#if GCRED
#define GCREDIND(x) do { NODEPTR nn = (x); mark(&nn); SETINDIR(n, nn); goto fin; } while(0)
   case T_INT:
#if INTTABLE
    if (LOW_INT <= (val = GETVALUE(n)) && val < HIGH_INT) {
      SETINDIR(n, intTable[val - LOW_INT]);
      COUNT(red_int);
      goto top;
    }
    goto fin;
#endif  /* INTTABLE */
   case T_AP:
      if (want_gc_red) {
        NODEPTR fun = indir(&FUN(n));
        NODEPTR arg = indir(&ARG(n));
        enum node_tag funt = GETTAG(fun);
        enum node_tag argt = GETTAG(arg);
        enum node_tag funfunt = funt == T_AP ? GETTAG(indir(&FUN(fun))) : T_FREE;
        enum node_tag funargt = argt == T_AP ? GETTAG(indir(&FUN(arg))) : T_FREE;

        /* This is really only fruitful just after parsing.  It can be removed. */
        if (funfunt == T_A) {
          /* Do the A x y --> y reduction */
          NODEPTR y = ARG(n);
          COUNT(red_a);
          GCREDIND(y);
        }

        if (funfunt == T_K) {
          /* Do the K x y --> x reduction */
          NODEPTR x = ARG(FUN(n));
          COUNT(red_k);
          GCREDIND(x);
        }

        if (funt == T_I) {
          /* Do the I x --> x reduction */
          NODEPTR x = ARG(n);
          COUNT(red_i);
          GCREDIND(x);
        }

        if(funt == T_CC && argt == T_I) { 
          /* C' I --> C */
          SETTAG(n, T_C);
          COUNT(red_cci);
          goto top;
        }

        if(funt == T_CCB && argt == T_AP) {
          NODEPTR funarg = indir(&FUN(arg));
          NODEPTR argarg = indir(&ARG(arg));
          if (GETTAG(argarg) == T_P && GETTAG(funarg) == T_AP) {
            if (GETTAG(indir(&FUN(funarg))) == T_B && GETTAG(indir(&ARG(funarg))) == T_C) { 
              /* C'B ((B C) P) --> C */
              SETTAG(n, T_C);
              COUNT(red_ccbbcp);
              goto top;
            }
          }
        }

        if(funt == T_B && argt == T_I) { 
          /* B I --> I */
          SETTAG(n, T_I);
          COUNT(red_bi);
          goto top;
        }

        if(funfunt == T_B && argt == T_I) { 
          /* B x I --> x */
          NODEPTR x = ARG(FUN(n));
          COUNT(red_bxi);
          GCREDIND(x);
        }

        if(funfunt == T_CCB && argt == T_I) { 
          /* C'B x I --> x */
          NODEPTR x = ARG(FUN(n));
          COUNT(red_ccbi);
          GCREDIND(x);
        }

        if(funt == T_C && funargt == T_C) { 
          /* C (C x) --> x */
          NODEPTR x = ARG(ARG(n));
          COUNT(red_cc);
          GCREDIND(x);
        }

#if 0
        /* Very rare */
        if (funt == T_S && funargt == T_K) {
          /* S (K x) --> B x */
          printf("SK"); fflush(stdout);
        }
#endif

#if 0
        /* Fairly frequent, but needs allocation */
        if (funfunt == T_B && funargt == T_K) {
          /* B x (K y) --> K x y */
          printf("BxK\n");
        }
#endif

#if 1
        if (funt == T_C) {
          enum node_tag tf;
          if ((tf = flip_ops[argt])) {
            /* Do the C op --> flip_op reduction */
            // PRINT("%s -> %s\n", tag_names[tt], tag_names[tf]);
            COUNT(red_flip);
            GCREDIND(HEAPREF(tf));
          }
        }
#endif
      }
#else   /* GCRED */
   case T_AP:
#endif  /* GCRED */
    /* Avoid tail recursion */
    np = &FUN(n);
    to_push = &ARG(n);
    break;
   case T_ARR:
    {
      struct ioarray *arr = ARR(n);

      // arr->marked records marking progress through arr.
      if (arr->marked >= arr->size) {
        goto fin;
      }
      // We unmark the array as a whole and push it as long
      // as there's more entries to scan.
      mark_unused(n);
      num_marked--;
      to_push = np;
      np = &arr->array[arr->marked++];
      break;
    }

   case T_FORPTR:
     FORPTR(n)->finalizer->marked = 1;
     goto fin;

   case T_THID:
     mark_thread(THR(n));
     break;

   case T_MVAR:
     mark_mvar(MVAR(n));
     break;

   default:
     goto fin;
  }

  if (!is_marked_used(*to_push)) {
    //  mark_depth++;
    PUSH((NODEPTR)to_push);
  }
  goto top;
 fin:
  //  if (mark_depth > max_mark_depth) {
  //    max_mark_depth = mark_depth;
  //  }
  //  mark_depth--;
  if (stack_ptr > stk) {
    np = (NODEPTR *)POPTOP();
    goto top;
  }
  return;
}

/* Perform a garbage collection:
   - Mark nodes from the stack
   - Mark permanent arrays
   - Mark threads that have a root
   - Scan and free arrays
   - Scan and free foreign pointers and run finalizers
   - Scan and free threads
   - Scan and free mvars
*/
void
gc(void)
{
  stackptr_t i;

  num_gc++;
  num_marked = 0;
#if WANT_STDIO
  if (verbose > 1)
    PRINT("gc mark\n");
#endif
  gc_mark_time -= GETTIMEMILLI();
  mark_all_free();
  /* Mark everything reachable from the stack */
  for (i = 0; i <= stack_ptr; i++)
    mark(&stack[i]);

  /* Mark everything reachable from permanent array nodes */
  for (struct ioarray *arr = array_root; arr; arr = arr->next) {
    if (arr->permanent) {
      for (i = 0; i < arr->size; i++)
        mark(&arr->array[i]);
    }
  }

  /* Mark everything reachable from the threads.
   * Note, zombie threads have no root so they are not marked.
   */
  for (struct mthread *mt = all_threads; mt; mt = mt->mt_next) {
    if (mt->mt_root != NIL)
      mark_thread(mt);
  }

  gc_mark_time += GETTIMEMILLI();

  if (num_marked > max_num_marked)
    max_num_marked = num_marked;
  num_free = heap_size - heap_start - num_marked;
  if (num_free < heap_size / 50)
    ERR("heap exhausted");

  gc_scan_time -= GETTIMEMILLI();
  /* Free unused arrays */
  for (struct ioarray **arrp = &array_root; *arrp; ) {
    struct ioarray *arr = *arrp;
    if (arr->marked || arr->permanent) {
      arr->marked = 0;
      arrp = &arr->next;
    } else {
      *arrp = arr->next;        /* unlink */
      num_arr_free++;
      FREE(arr);                /* and FREE */
    }
  }

  /* Run finalizers on unused foreign pointers. */
  for (struct final **finp = &final_root; *finp; ) {
    struct final *fin = *finp;
    if (fin->marked) {
      fin->marked = 0;
      finp = &fin->next;
    } else {
      /* Unused, run finalizer and free all associated memory */
      if (fin->size == NOSIZE) {
        num_fin_free++;
      } else {
        num_bs_free++;
        num_bs_inuse -= fin->size;
        if (num_bs_alloc - num_bs_free > num_bs_alloc_max)
          num_bs_alloc_max = num_bs_alloc - num_bs_free;
      }
      void (*f)(void *) = (void (*)(void *))fin->final;
      //printf("forptr free fin=%p, f=%p", fin, f);
      //fflush(stdout);
      if (f) {
        //printf("finalizer fin=%p final=%p\n", fin, f);
        (*f)(fin->arg);
      }
      for (struct forptr *p = fin->back; p; ) {
        struct forptr *q = p->next;
        //printf("free fp=%p\n", p);
        //printf(" p=%p desc=%s", p, p->desc ? p->desc : "NONE");
        //fflush(stdout);
        FREE(p);
        //memset(p, 0x55, sizeof *p);
        p = q;
      }
      //printf("\n");
      *finp = fin->next;
      //printf("free fin=%p\n", fin);
      FREE(fin);
      //memset(fin, 0x77, sizeof *fin);
    }
  }

  /* Remove unreferenced zombie threads */
  for (struct mthread **mtp = &all_threads; *mtp; ) {
    struct mthread *mt = *mtp;
    if ((mt->mt_state == ts_died || mt->mt_state == ts_finished) && !mt->mt_mark) {
      COUNT(num_thread_reap);
      *mtp = mt->mt_next;
      free(mt);
    } else {
      mt->mt_mark = 0;
      mtp = &mt->mt_next;
    }
  }
  
  /* Remove unreferences mvars */
  for (struct mvar **mvp = &all_mvars; *mvp; ) {
    struct mvar *mv = *mvp;
    if (!mv->mv_mark) {
      COUNT(num_mvar_free);
      *mvp = mv->mv_next;
      free(mv);
    } else {
      mv->mv_mark = 0;
      mvp = &mv->mv_next;
    }
  }

  gc_scan_time += GETTIMEMILLI();

#if WANT_STDIO
  if (verbose > 1) {
    PRINT("gc done, %"PRIcounter" free\n", num_free);
    /*PRINT(" GC reductions A=%"PRIcounter", K=%"PRIcounter", I=%"PRIcounter", int=%"PRIcounter" flip=%"PRIcounter"\n",
      red_a, red_k, red_i, red_int, red_flip);*/
  }
  if (gcbell) {
    fputc('\007', stderr);      /* ring the bell */
    fflush(stderr);
  }
#endif  /* !WANT_STDIO */

#if 0
  /* For debugging only: mark all free cells */
  for(int n = 0; n < heap_size; n++) {
    NODEPTR p = HEAPREF(n);
    if (!is_marked_used(p)) {
      SETTAG(p, T_FREE);
    }
  }
#endif
}

static INLINE
value_t
peekWord(value_t *p)
{
  return *p;
}

static INLINE
void
pokeWord(value_t *p, value_t w)
{
  *p = w;
}

static INLINE
void *
peekPtr(void **p)
{
  return *p;
}

static INLINE
void
pokePtr(void **p, void *w)
{
  *p = w;
}

static INLINE
uvalue_t
peek_uint8(uint8_t *p)
{
  return *p;
}

static INLINE
void
poke_uint8(uint8_t *p, value_t w)
{
  *p = (uint8_t)w;
}

static INLINE
uvalue_t
peek_uint16(uint16_t *p)
{
  return *p;
}

static INLINE
void
poke_uint16(uint16_t *p, value_t w)
{
  *p = (uint16_t)w;
}

#if WORD_SIZE >= 32
static INLINE
uvalue_t
peek_uint32(uint32_t *p)
{
  return *p;
}

static INLINE
void
poke_uint32(uint32_t *p, value_t w)
{
  *p = (uint32_t)w;
}
#endif  /* WORD_SIZE >= 32 */

#if WORD_SIZE >= 64
static INLINE
uvalue_t
peek_uint64(uint64_t *p)
{
  return *p;
}

static INLINE
void
poke_uint64(uint64_t *p, value_t w)
{
  *p = (uint64_t)w;
}
#endif  /* WORD_SIZE >= 64 */

static INLINE
value_t
peek_int8(int8_t *p)
{
  return *p;
}

static INLINE
void
poke_int8(int8_t *p, value_t w)
{
  *p = (int8_t)w;
}

static INLINE
value_t
peek_int16(int16_t *p)
{
  return *p;
}

static INLINE
void
poke_int16(int16_t *p, value_t w)
{
  *p = (int16_t)w;
}

#if WORD_SIZE >= 32
static INLINE
value_t
peek_int32(int32_t *p)
{
  return *p;
}

static INLINE
void
poke_int32(int32_t *p, value_t w)
{
  *p = (int32_t)w;
}
#endif  /* WORD_SIZE >= 32 */

#if WORD_SIZE >= 64
static INLINE
value_t
peek_int64(int64_t *p)
{
  return *p;
}

static INLINE
void
poke_int64(int64_t *p, value_t w)
{
  *p = (int64_t)w;
}
#endif  /* WORD_SIZE >= 64 */

static INLINE
value_t
peek_int(int *p)
{
  return *p;
}

static INLINE
void
poke_int(int *p, value_t w)
{
  *p = (int)w;
}

static INLINE
value_t
peek_uint(unsigned int *p)
{
  return *p;
}

static INLINE
void
poke_uint(unsigned int *p, value_t w)
{
  *p = (unsigned int)w;
}

static INLINE
value_t
peek_short(short *p)
{
  return *p;
}

static INLINE
void
poke_short(short *p, value_t w)
{
  *p = (short)w;
}

static INLINE
value_t
peek_ushort(unsigned short *p)
{
  return *p;
}

static INLINE
void
poke_ushort(unsigned short *p, value_t w)
{
  *p = (unsigned short)w;
}

static INLINE
value_t
peek_long(long *p)
{
  return *p;
}

static INLINE
void
poke_long(long *p, value_t w)
{
  *p = (long)w;
}

static INLINE
value_t
peek_ulong(unsigned long *p)
{
  return *p;
}

static INLINE
void
poke_ulong(unsigned long *p, value_t w)
{
  *p = (unsigned long)w;
}

static INLINE
value_t
peek_llong(long long *p)
{
  return *p;
}

static INLINE
void
poke_llong(long long *p, value_t w)
{
  *p = (long long)w;
}

static INLINE
value_t
peek_ullong(unsigned long long *p)
{
  return *p;
}

static INLINE
void
poke_ullong(unsigned long long *p, value_t w)
{
  *p = (unsigned long long)w;
}

static INLINE
value_t
peek_size_t(size_t *p)
{
  return *p;
}

static INLINE
void
poke_size_t(size_t *p, value_t w)
{
  *p = (size_t)w;
}

#if WANT_FLOAT
static INLINE
flt_t
peek_flt(flt_t *p)
{
  return *p;
}

static INLINE
void
poke_flt(flt_t *p, flt_t w)
{
  *p = w;
}
#endif  /* WANT_FLOAT */

/* Look up an FFI function by name */
value_t
lookupFFIname(const char *name)
{
  size_t i;

  for(i = 0; ffi_table[i].ffi_name; i++)
    if (strcmp(ffi_table[i].ffi_name, name) == 0)
      return (value_t)i;
  if (xffi_table) {
    for(i = 0; xffi_table[i].ffi_name; i++)
      if (strcmp(xffi_table[i].ffi_name, name) == 0)
        return (value_t)(i + num_ffi);
  }
  return -1;
}

NODEPTR
ffiNode(const char *buf)
{
  NODEPTR r;
  value_t i = lookupFFIname(buf);
  char *fun;

  if (i < 0) {
    /* lookup failed, generate a node that will dynamically generate an error */
    r = alloc_node(T_BADDYN);
    fun = mmalloc(strlen(buf) + 1);
    strcpy(fun, buf);
    CSTR(r) = fun;
  } else {
    r = alloc_node(T_IO_CCALL);
    SETVALUE(r, i);
  }
  return r;
}

/* If the next input character is c, then consume it, else leave it alone. */
int
gobble(BFILE *f, int c)
{
  int d = getb(f);
  if (c == d) {
    return 1;
  } else {
    ungetb(d, f);
    return 0;
  }
}

/* Get a non-terminating character.  ' ' and '\n' terminates a token. */
int
getNT(BFILE *f)
{
  int c;

  c = getb(f);
  if (c == ' ' || c == '\n') {
    return 0;
  } else {
    return c;
  }
}

value_t
parse_int(BFILE *f)
{
  // Parse using uvalue_t, which wraps on overflow.
  uvalue_t i = 0;
  int neg = 1;
  int c = getb(f);
  if (c == '-') {
    neg = -1;
    c = getb(f);
  }
  for(;;) {
    i = i * 10 + (c - '0');
    c = getb(f);
    if (c < '0' || c > '9') {
      ungetb(c, f);
      break;
    }
  }
  // Multiply by neg without triggering undefined behavior.
  return (value_t)(((uvalue_t)neg) * i);
}

#if WANT_FLOAT
flt_t
parse_double(BFILE *f)
{
  // apparently longest float, when rendered, takes up 24 characters. We add one more for a potential
  // minus sign, and another one for the final null terminator.
  // https://stackoverflow.com/questions/1701055/what-is-the-maximum-length-in-chars-needed-to-represent-any-double-value
  char buf[26];
  for(int j = 0; (buf[j] = getNT(f)); j++)
    ;

  return strtod(buf, NULL);
}
#endif

struct forptr *mkForPtr(struct bytestring bs);
NODEPTR mkFunPtr(HsFunPtr p);

/* Create a forptr that has a free() finalizer. */
struct forptr *
mkForPtrFree(struct bytestring str)
{
  struct forptr *fp = mkForPtr(str);         /* Create a foreign pointer */
  fp->finalizer->final = (HsFunPtr)FREE;     /* and set the finalizer to just free it */
  return fp;
}

NODEPTR
mkStrNode(struct bytestring str)
{
  NODEPTR n = alloc_node(T_FORPTR);
  struct forptr *fp = mkForPtrFree(str);
  FORPTR(n) = fp;
  fp->finalizer->fptype = FP_BSTR;
  //printf("mkForPtr n=%p fp=%p %d %s payload.string=%p\n", n, fp, (int)FORPTR(n)->payload.size, (char*)FORPTR(n)->payload.string, FORPTR(n)->payload.string);
  return n;
}

/* Table of labelled nodes for sharing during parsing. */
struct shared_entry {
  heapoffs_t label;
  NODEPTR node;                 /* NIL indicates unused */
} *shared_table;
heapoffs_t shared_table_size;

/* Look for the label in the table.
 * If it's found, return the node.
 * If not found, return the first empty entry.
*/
NODEPTR *
find_label(heapoffs_t label)
{
  int i;

  for(i = (int)label; ; i++) {
    i %= shared_table_size;
    if (shared_table[i].node == NIL) {
      /* The slot is empty, so claim and return it */
      shared_table[i].label = label;
      return &shared_table[i].node;
    } else if (shared_table[i].label == label) {
      /* Found the label, so return it. */
      return &shared_table[i].node;
    }
    /* Not empty and not found, try next. */
  }
}

/* The memory allocated here is never freed.
 * This could be fixed by using a forptr and a
 * finalizer for read UTF-8 strings.
 * Fix this if there is a lot of deserialization.
 */
struct bytestring
parse_string(BFILE *f)
{
  struct bytestring bs;
  size_t sz = 20;
  uint8_t *buffer = mmalloc(sz);
  size_t i;
  int c;

  for(i = 0;;) {
    c = getb(f);
    if (c == '"')
      break;
    if (i >= sz - 1) {
      sz *= 2;
      buffer = mrealloc(buffer, sz);
    }
#if 0
    if (c == '\\') {
      buffer[i++] = (uint8_t)parse_int(f);
      if (!gobble(f, '&'))
        ERR("parse string");
    } else {
      buffer[i++] = c;
    }
#else
    /* See src/MicroHs/ExpPrint.hs for how strings are encoded. */
    switch (c) {
    case '\\':
      c = getb(f);
      if (c == '?')
        c = 0x7f;
      else if (c == '_')
        c = 0xff;
      break;
    case '^':
      c = getb(f);
      if (c < 0x40)
        c &= 0x1f;
      else
        c = (c & 0x1f) | 0x80;
      break;
    case '|':
      c = getb(f);
      c |= 0x80;
      break;
    default:
      /* Unencoded */
      ;
    }
    buffer[i++] = c;
#endif
  }
  buffer[i] = 0;                /* add a trailing 0 in case we need a C string */
  buffer = mrealloc(buffer, i + 1);

  bs.size = i;
  bs.string = buffer;
  //printf("parse_string %d %s\n", (int)bs.size, (char*)bs.string);
  return bs;
}

struct forptr *new_mpz(void);

NODEPTR
parse(BFILE *f)
{
  stackptr_t stk = stack_ptr;
  NODEPTR r, x, y;
  NODEPTR *nodep;
  heapoffs_t l;
  value_t i;
  int c;
  size_t j;
  char buf[80];                 /* store names of primitives. */

  for(;;) {
    c = getb(f);
    if (c < 0) ERR("parse EOF");
    switch (c) {
    case ' ':
    case '\n':
      continue;
    }
    if (num_free < 3)
      ERR("out of heap reading code");
    GCCHECK(1);
    switch(c) {
    case '@':
      x = TOP(0);
      y = TOP(1);
      POP(2);
      PUSH(new_ap(y, x));
      break;
    case '}':
      x = TOP(0);
      POP(1);
      if (stack_ptr != stk)
        ERR("parse: stack");
      return x;
#if WANT_GMP
    case '%':
      {
        struct bytestring bs = parse_string(f); /* get all the digits, terminated by " */
        struct forptr *fp = new_mpz();          /* a new mpz */
        mpz_ptr op = fp->payload.string;        /* get actual pointer */
        mpz_set_str(op, bs.string, 10);         /* convert to an mpz */
        free(bs.string);
        r = alloc_node(T_FORPTR);
        FORPTR(r) = fp;
        PUSH(r);
        break;
      }
#endif
    case '&':
#if WANT_FLOAT
      r = mkFlt(parse_double(f));
#else
      while (getNT(f))          /* skip the float constant */
        ;
      r = alloc_node(T_DBL);
      SETVALUE(r, 0);
#endif
      PUSH(r);
      break;
    case '#':
      i = parse_int(f);
      r = mkInt(i);
      PUSH(r);
      break;
    case '[':
      {
        size_t sz;
        struct ioarray *arr;
        size_t i;
        sz = (size_t)parse_int(f);
        if (!gobble(f, ']')) ERR("parse arr 1");
        arr = arr_alloc(sz, NIL);
        for (i = 0; i < sz; i++) {
          arr->array[i] = TOP(sz - i - 1);
        }
        r = alloc_node(T_ARR);
        ARR(r) = arr;
        POP(sz);
        PUSH(r);
        break;
      }
    case '_':
      /* Reference to a shared value: _label */
      l = parse_int(f);  /* The label */
      nodep = find_label(l);
      if (*nodep == NIL) {
        /* Not yet defined, so make it an indirection */
        *nodep = alloc_node(T_FREE);
        SETINDIR(*nodep, NIL);
      }
      PUSH(*nodep);
      break;
    case ':':
      /* Define a shared expression: :label e */
      l = parse_int(f);  /* The label */
      if (!gobble(f, ' ')) ERR("parse ' '");
      nodep = find_label(l);
      x = TOP(0);
      if (*nodep == NIL) {
        /* not referenced yet, so add a direct reference */
        *nodep = x;
      } else {
        /* Sanity check */
        if (GETTAG(*nodep) != T_IND || GETINDIR(*nodep) != NIL) ERR("shared != NIL");
        SETINDIR(*nodep, x);
      }
      break;
    case '"':
      /* Everything up to the next " is a string.
       * Special characters are encoded as \NNN&,
       * where NNN is the decimal value of the character */
      PUSH(mkStrNode(parse_string(f)));
      break;
#if WANT_TICK
    case '!':
      if (!gobble(f, '"'))
        ERR("parse !");
      i = add_tick_table(parse_string(f));
      r = alloc_node(T_TICK);
      SETVALUE(r, (value_t)i);
      PUSH(r);
      break;
#endif
    case '^':
      /* An FFI name */
      for (j = 0; (buf[j] = getNT(f)); j++)
        ;
      r = ffiNode(buf);
      PUSH(r);
      break;
    case ';':
      /* <name is a C function pointer to name */
      for (j = 0; (buf[j] = getNT(f)); j++)
        ;
      if (strcmp(buf, "0") == 0) {
        PUSH(mkFunPtr((HsFunPtr)0));
      } else if (strcmp(buf, "closeb") == 0) {
        PUSH(mkFunPtr((HsFunPtr)closeb));
      } else {
        ERR1("unknown funptr '%s'", buf);
      }
      break;
    default:
      buf[0] = c;
      /* A primitive, keep getting char's until end */
      for (j = 1; (buf[j] = getNT(f)); j++)
        ;
      /* Look up the primop and use the preallocated node. */
      for (j = 0; j < sizeof primops / sizeof primops[0]; j++) {
        if (strcmp(primops[j].name, buf) == 0) {
          r = primops[j].node;
          goto found;
        }
      }
      ERR1("no primop %s", buf);
    found:
      PUSH(r);
      break;
    }
  }
}

void
checkversion(BFILE *f)
{
  char *p = VERSION;
  int c;

  while ((c = *p++)) {
    if (c != getb(f))
      ERR("version mismatch");
  }
  (void)gobble(f, '\r');                 /* allow extra CR */
}

/* Parse a file */
NODEPTR
parse_top(BFILE *f)
{
  heapoffs_t numLabels, i;
  NODEPTR n;
  checkversion(f);
  numLabels = parse_int(f);
  if (!gobble(f, '\n'))
    ERR("size parse");
  gobble(f, '\r');                 /* allow extra CR */
  shared_table_size = 3 * numLabels; /* sparsely populated hashtable */
  shared_table = mmalloc(shared_table_size * sizeof(struct shared_entry));
  for(i = 0; i < shared_table_size; i++)
    shared_table[i].node = NIL;
  n = parse(f);
  FREE(shared_table);
  return n;
}

#if WANT_STDIO
NODEPTR
parse_file(const char *fn, size_t *psize)
{
  FILE *f = fopen(fn, "r");
  if (!f)
    ERR1("file not found %s", fn);

  /* And parse it */
  BFILE *p = add_FILE(f);
  NODEPTR n = parse_top(p);
  *psize = ftell(f);
  closeb(p);
  return n;
}
#endif  /* WANT_STDIO */

counter_t num_shared;

/* Two bits per node: marked, shared
 * 0, 0   -- not visited
 * 1, 0   -- visited once
 * 1, 1   -- visited more than once
 * 0, 1   -- printed
 */
struct print_bits {
  bits_t *marked_bits;
  bits_t *shared_bits;
};
static INLINE void set_bit(bits_t *bits, NODEPTR n)
{
  heapoffs_t i = LABEL(n);
  bits[i / BITS_PER_WORD] |= (1ULL << (i % BITS_PER_WORD));
}
#if WANT_STDIO
static INLINE void clear_bit(bits_t *bits, NODEPTR n)
{
  heapoffs_t i = LABEL(n);
  bits[i / BITS_PER_WORD] &= ~(1ULL << (i % BITS_PER_WORD));
}
#endif
static INLINE int test_bit(bits_t *bits, NODEPTR n)
{
  heapoffs_t i = LABEL(n);
  return (bits[i / BITS_PER_WORD] & (1ULL << (i % BITS_PER_WORD))) != 0;
}

size_t strNodes(size_t len);
NODEPTR mkStringC(char *str);

#if WANT_STDIO
#if WORD_SIZE == 64
#define CONVDBL "%.16g"
#elif WORD_SIZE == 32
#define CONVDBL "%.8g"
#endif
void
convdbl(char *str, flt_t x)
{
  /* Using 16 decimals will lose some precision.
   * 17 would keep the precision, but it frequently looks very ugly.
   */
  (void)snprintf(str, 25, CONVDBL, x);
  if (strcmp(str, "nan") != 0 && strcmp(str, "-nan") != 0 &&
      strcmp(str, "inf") != 0 && strcmp(str, "-inf") != 0 &&
      !strchr(str, '.') && !strchr(str, 'e') && !strchr(str, 'E')) {
    /* There is no decimal point and no exponent, so add a decimal point */
    strcat(str, ".0");
  }
}

NODEPTR
dblToString(flt_t x)
{
  char str[30];
  convdbl(str, x);
  // turn it into a mhs string
  GCCHECK(strNodes(strlen(str)));
  return mkStringC(str);
}

void
putdblb(flt_t x, BFILE *p)
{
  char str[30];
  convdbl(str, x);
  putsb(str, p);
}

void printrec(BFILE *f, struct print_bits *pb, NODEPTR n, int prefix);

/* Mark all reachable nodes, when a marked node is reached, mark it as shared. */
void
find_sharing(struct print_bits *pb, NODEPTR n)
{
 top:
  while (GETTAG(n) == T_IND) {
    n = GETINDIR(n);
  }
  if (n < cells || n >= cells + heap_size) abort();
  //PRINT("find_sharing %p %llu ", n, LABEL(n));
  tag_t tag = GETTAG(n);
  if (tag == T_AP || tag == T_ARR || tag == T_FORPTR) {
    if (test_bit(pb->shared_bits, n)) {
      /* Alread marked as shared */
      //PRINT("shared\n");
      ;
    } else if (test_bit(pb->marked_bits, n)) {
      /* Already marked, so now mark as shared */
      //PRINT("marked\n");
      set_bit(pb->shared_bits, n);
      num_shared++;
    } else {
      /* Mark as visited, and recurse */
      //PRINT("unmarked\n");
      set_bit(pb->marked_bits, n);
      switch(tag) {
      case T_AP:
        find_sharing(pb, FUN(n));
        n = ARG(n);
        goto top;
      case T_ARR:
        for(size_t i = 0; i < ARR(n)->size; i++) {
          find_sharing(pb, ARR(n)->array[i]);
        }
        break;
      default:
        break;
      }
    }
  } else {
    /* Not an sharable node, so do nothing */
    //PRINT("not T_AP\n");
    ;
  }
}

void
print_string(BFILE *f, struct bytestring bs)
{
  uint8_t *str = bs.string;
  putb('"', f);
  for (size_t i = 0; i < bs.size; i++) {
    int c = str[i];
#if 0
    if (c == '"' || c == '\\' || c < ' ' || c > '~') {
      putb('\\', f);
      putdecb(c, f);
      putb('&', f);
    } else {
      putb(c, f);
    }
#else
    if (c < 0 || c > 0xff)
      ERR("print_string");
    if (c < 0x20) {
      putb('^', f); putb(c + 0x20, f);
    } else if (c == '"' || c == '^' || c == '|' || c == '\\') {
      putb('\\', f); putb(c, f);
    } else if (c < 0x7f) {
      putb(c, f);
    } else if (c == 0x7f) {
      putb('\\', f); putb('?', f);
    } else if (c < 0xa0) {
      putb('^', f); putb(c - 0x80 + 0x40, f);
    } else if (c < 0xff) {
      putb('|', f); putb(c - 0x80, f);
    } else {                    /* must be< c == 0xff */
      putb('\\', f); putb('_', f);
    }
#endif
  }
  putb('"', f);
}

/*
 * Recursively print an expression.
 * This assumes that the shared nodes has been marked as such.
 * The prefix flag is used to get a readable dump.
 */
void
printrec(BFILE *f, struct print_bits *pb, NODEPTR n, int prefix)
{
  int share = 0;
  enum node_tag tag;
  char prbuf[30];

  while (GETTAG(n) == T_IND) {
    /*putb('*', f);*/
    n = GETINDIR(n);
  }

  if (test_bit(pb->shared_bits, n)) {
    /* The node is shared */
    if (test_bit(pb->marked_bits, n)) {
      /* Not yet printed, so emit a label */
      if (prefix) {
        putb(':', f);
        putdecb((value_t)LABEL(n), f);
        putb(' ', f);
      } else {
        share = 1;
      }
      clear_bit(pb->marked_bits, n);  /* mark as printed */
    } else {
      /* This node has already been printed, so just use a reference. */
      putb('_', f);
      putdecb((value_t)LABEL(n), f);
      if (!prefix)
        putb(' ', f);
      return;
    }
  }

  //if (n == atptr) putb('@', f);
  tag = GETTAG(n);
  switch (tag) {
  case T_AP:
    if (prefix) {
      putb('(', f);
      printrec(f, pb, FUN(n), prefix);
      putb(' ', f);
      printrec(f, pb, ARG(n), prefix);
      putb(')', f);
    } else {
      printrec(f, pb, FUN(n), prefix);
      printrec(f, pb, ARG(n), prefix);
      putb('@', f);
    }
    break;
  case T_INT: putb('#', f); putdecb(GETVALUE(n), f); break;
  case T_DBL: putb('&', f); putdblb(GETDBLVALUE(n), f); break;
  case T_ARR:
    if (prefix) {
      /* Arrays serialize as '[sz] e_1 ... e_sz' */
      putb('[', f);
      putdecb((value_t)ARR(n)->size, f);
      putb(']', f);
      for(size_t i = 0; i < ARR(n)->size; i++) {
        putb(' ', f);
        printrec(f, pb, ARR(n)->array[i], prefix);
      }
    } else {
      /* Arrays serialize as 'e_1 ... e_sz [sz]' */
      for(size_t i = 0; i < ARR(n)->size; i++) {
        printrec(f, pb, ARR(n)->array[i], prefix);
      }
      putb('[', f);
      putdecb((value_t)ARR(n)->size, f);
      putb(']', f);
    }
    break;
  case T_PTR:
    if (prefix) {
      snprintf(prbuf, sizeof prbuf, "PTR<%p>",PTR(n));
      putsb(prbuf, f);
    } else {
      ERR("Cannot serialize pointers");
    }
    break;
  case T_FUNPTR:
    /* There are a few function pointers that happen without user FFI.
     * We need to be able to serialize these.
     * XXX Make a table if we need more.
     */
    if (FUNPTR(n) == 0) {
      putsb(";0 ", f);
    } else if (FUNPTR(n) == (HsFunPtr)closeb) {
      putsb(";closeb ", f);
    } else if (prefix) {
      snprintf(prbuf, sizeof prbuf, "FUNPTR<%p>",FUNPTR(n));
      putsb(prbuf, f);
    } else {
      ERR1("Cannot serialize function pointers %p", FUNPTR(n));
    }
    break;
  case T_THID:
    if (prefix) {
      snprintf(prbuf, sizeof prbuf, "FUNPTR<%d>",(int)THR(n)->mt_id);
    } else {
      ERR("cannot serialize ThreadId yet");
    }
  case T_FORPTR:
    if (n == comb_stdin)
      putsb("IO.stdin", f);
    else if (n == comb_stdout)
      putsb("IO.stdout", f);
    else if (n == comb_stderr)
      putsb("IO.stderr", f);
#if WANT_GMP
    else if (FORPTR(n)->finalizer->fptype == FP_MPZ) {
      /* Serialize as %99999" */
      mpz_ptr op = FORPTR(n)->payload.string; /* get the mpz */
      int sz = mpz_sizeinbase(op, 10);        /* maximum length */
      char *s = mmalloc(sz + 2);
      (void)mpz_get_str(s, 10, op);           /* convert to a string */
      putsb("%", f);
      putsb(s, f);
      putsb("\"", f);                         /* so we can use parse_string */
      free(s);
    }
#endif  /* WANT_GMP */
    else if (FORPTR(n)->finalizer->fptype == FP_BSTR) {
      print_string(f, FORPTR(n)->payload);
    } else if (prefix) {
      snprintf(prbuf, sizeof prbuf, "FORPTR<%p>",FORPTR(n));
      putsb(prbuf, f);
    } else {
      ERR("Cannot serialize foreign pointers");
    }
    break;
  case T_IO_CCALL: putb('^', f); putsb(FFI_IX(GETVALUE(n)).ffi_name, f); break;
  case T_BADDYN: putb('^', f); putsb(CSTR(n), f); break;
  case T_TICK:
    putb('!', f);
    print_string(f, tick_table[GETVALUE(n)].tick_name);
    break;
  default:
    if (0 <= tag && tag <= T_LAST_TAG)
      if (tag_names[tag])
        putsb(tag_names[tag], f);
      else {
        snprintf(prbuf, sizeof prbuf, "TAG=%d", (int)tag);
        putsb(prbuf, f);
      }
    else {
      snprintf(prbuf, sizeof prbuf, "BADTAG(%d)", (int)tag);
      putsb(prbuf, f);
    }
    break;
  }
  if (!prefix) {
    if (GETTAG(n) != T_AP)
      putb(' ', f);
    if (share) {
      putb(':', f);
      putdecb((value_t)LABEL(n), f);
      putb(' ', f);
    }
  }
}

/* Serialize a graph to file. */
void
printb(BFILE *f, NODEPTR n, int header)
{
  struct print_bits pb;
  num_shared = 0;
  pb.marked_bits = mcalloc(free_map_nwords, sizeof(bits_t));
  pb.shared_bits = mcalloc(free_map_nwords, sizeof(bits_t));
  find_sharing(&pb, n);
  if (header) {
    putsb(VERSION, f);
    putdecb(num_shared, f);
    putb('\n', f);
  }
  printrec(f, &pb, n, !header);
  if (header) {
    putb('}', f);
  }
  FREE(pb.marked_bits);
  FREE(pb.shared_bits);
}

/* Show a graph. */
void
pps(NODEPTR n)
{
  pp(stdout, n);
}

void
pp(FILE *f, NODEPTR n)
{
  BFILE *bf = add_FILE(f);
  printb(bf, n, 0);
  putb('\n', bf);
  freeb_file(bf);
}

#if 0
void
ppmsg(const char *msg, NODEPTR n)
{
  printf("%s", msg);
  pp(stdout, n);
  printf("\n");
}

void
dump(const char *msg, NODEPTR at)
{
  atptr = at;
  printf("dump: %s\n", msg);
  pp(stdout, *topnode);
}
#endif

#else  /* WANT_STDIO */
NODEPTR
dblToString(flt_t x)
{
  return mkStringC("no dblToString");
}

#endif  /* WANT_STDIO */

NODEPTR
mkInt(value_t i)
{
#if INTTABLE
  if (LOW_INT <= i && i < HIGH_INT) {
    return intTable[i - LOW_INT];
  }
#endif

  NODEPTR n;
  n = alloc_node(T_INT);
  SETVALUE(n, i);
  return n;
}

NODEPTR
mkFlt(flt_t d)
{
  NODEPTR n;
  n = alloc_node(T_DBL);
  SETDBLVALUE(n, d);
  return n;
}

NODEPTR
mkPtr(void* p)
{
  NODEPTR n;
  n = alloc_node(T_PTR);
  PTR(n) = p;
  return n;
}

NODEPTR
mkFunPtr(void (*p)(void))
{
  NODEPTR n;
  n = alloc_node(T_FUNPTR);
  FUNPTR(n) = p;
  return n;
}

struct forptr*
mkForPtr(struct bytestring bs)
{
  struct final *fin = mcalloc(1, sizeof(struct final));
  struct forptr *fp = mcalloc(1, sizeof(struct forptr));
  if (bs.size == NOSIZE) {
    num_fin_alloc++;
  } else {
    num_bs_alloc++;
    num_bs_inuse += bs.size;
    num_bs_bytes += bs.size;
    if (num_bs_inuse > num_bs_inuse_max)
      num_bs_inuse_max = num_bs_inuse;
  }
  //printf("mkForPtr p=%p fin=%p fp=%p\n", p, fin, fp);
  fin->next = final_root;
  final_root = fin;
  fin->final = 0;
  fin->arg = bs.string;
  fin->size = bs.size;          /* The size is not really needed */
  fin->back = fp;
  fin->marked = 0;
  fp->next = 0;
  fp->payload = bs;
  fp->finalizer = fin;
  //  fp->desc = 0;
  return fp;
}

struct forptr*
mkForPtrP(void *p)
{
  struct bytestring bs = { NOSIZE, p };
  return mkForPtr(bs);
}

struct forptr*
addForPtr(struct forptr *ofp, int s)
{
  struct forptr *fp = mmalloc(sizeof(struct forptr));
  struct final *fin = ofp->finalizer;

  fp->next = ofp;
  fin->back = fp;
  if (ofp->payload.size != NOSIZE)
    fp->payload.size = ofp->payload.size - s;
  fp->payload.string = (uint8_t*)ofp->payload.string + s;
  fp->finalizer = fin;
  return fp;
}

struct forptr*
bssubstr(struct forptr *fp, value_t offs, value_t len)
{
  struct forptr *res = addForPtr(fp, offs);
  res->payload.size = len;
  return res;
}

static INLINE NODEPTR
mkNil(void)
{
  return combFalse;
}

static INLINE NODEPTR
mkCons(NODEPTR x, NODEPTR xs)
{
  return new_ap(new_ap(combCons, x), xs);
}

size_t
strNodes(size_t len)
{
  /* Each character will need a CHAR node and a CONS node, a CONS uses 2 T_AP nodes */
  len *= (1 + 2);
  /* And each string will need a NIL */
  len += 1;
  return len;
}

/* Turn a C string into a combinator string.
 * Does NOT do UTF decoding.
 */
NODEPTR
mkString(struct bytestring bs)
{
  NODEPTR n, nc;
  size_t i;
  const unsigned char *str = bs.string; /* no sign bits, please */

  n = mkNil();
  for(i = bs.size; i > 0; i--) {
    nc = mkInt(str[i-1]);
    n = mkCons(nc, n);
  }
  return n;
}

NODEPTR
mkStringC(char *str)
{
  struct bytestring bs = { strlen(str), str };
  return mkString(bs);
}

NODEPTR
mkStringU(struct bytestring bs)
{
  BFILE *ubuf = add_utf8(openb_rd_buf(bs.string, bs.size));
  NODEPTR n, *np, nc;

  //printf("mkStringU %d %s\n", (int)bs.size, (char*)bs.string);

  n = mkNil();
  np = &n;
  for(;;) {
    int c = getb(ubuf);
    if (c < 0)
      break;
    nc = mkInt(c);
    *np = mkCons(nc, *np);
    np = &ARG(*np);
  }
  closeb(ubuf);
  return n;
}

NODEPTR
bsunpack(struct bytestring bs)
{
  NODEPTR n, *np, nc;
  size_t i;

  n = mkNil();
  np = &n;
  for(i = 0; i < bs.size; i++) {
    nc = mkInt(((uint8_t *)bs.string)[i]);
    *np = mkCons(nc, *np);
    np = &ARG(*np);
  }
  return n;
}

/* XXX This should somehow be merged with other utf8 decoders */
value_t
headutf8(struct bytestring bs, void **ret)
{
  uint8_t *p = bs.string;
  if (bs.size == 0)
    ERR("headUTF8 0");
  int c1 = *p++;
  if ((c1 & 0x80) == 0) {
    if (ret)
      *ret = p;
    return c1;
  }
  if (bs.size == 1)
    ERR("headUTF8 1");
  int c2 = *p++;
  if ((c1 & 0xe0) == 0xc0) {
    if (ret)
      *ret = p;
    return ((c1 & 0x1f) << 6) | (c2 & 0x3f);
  }
  if (bs.size == 2)
    ERR("headUTF8 2");
  int c3 = *p++;
  if ((c1 & 0xf0) == 0xe0) {
    if (ret)
      *ret = p;
    return ((c1 & 0x0f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
  }
  if (bs.size == 3)
    ERR("headUTF8 3");
  int c4 = *p++;
  if ((c1 & 0xf8) == 0xf0) {
    if (ret)
      *ret = p;
    return ((c1 & 0x07) << 18) | ((c2 & 0x3f) << 12) | ((c3 & 0x3f) << 6) | (c4 & 0x3f);
  }
  ERR("headUTF8 4");
}

/* Evaluate to an INT */
static INLINE value_t
evalint(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_INT) {
    ERR1("evalint, bad tag %d", GETTAG(n));
  }
#endif
  return GETVALUE(n);
}

/* Evaluate to a Flt_T */
static INLINE flt_t
evaldbl(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_DBL) {
    ERR1("evaldbl, bad tag %d", GETTAG(n));
  }
#endif
  return GETDBLVALUE(n);
}

/* Evaluate to a T_PTR */
void *
evalptr(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_PTR) {
    ERR1("evalptr, bad tag %d", GETTAG(n));
  }
#endif
  return PTR(n);
}

/* Evaluate to a T_FUNPTR */
HsFunPtr
evalfunptr(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_FUNPTR) {
    ERR1("evalfunptr, bad tag %d", GETTAG(n));
  }
#endif
  return FUNPTR(n);
}

/* Evaluate to a T_FORPTR */
struct forptr *
evalforptr(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_FORPTR) {
    ERR1("evalforptr, bad tag %d", GETTAG(n));
  }
#endif
  return FORPTR(n);
}

/* Evaluate to a bytestring */
struct forptr *
evalbstr(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_FORPTR || FORPTR(n)->finalizer->fptype != FP_BSTR) {
    ERR1("evalbstr, bad tag %d", GETTAG(n));
  }
#endif
  return FORPTR(n);
}

/* Evaluate to a T_THID */
struct mthread *
evalthid(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_THID) {
    ERR1("evalthid, bad tag %d", GETTAG(n));
  }
#endif
  return THR(n);
}

/* Evaluate to a T_MVAR */
struct mvar *
evalmvar(NODEPTR n)
{
  n = evali(n);
#if SANITY
  if (GETTAG(n) != T_MVAR) {
    ERR1("evalmvar, bad tag %d", GETTAG(n));
  }
#endif
  return MVAR(n);
}

/* Evaluate a string, returns a newly allocated buffer.
 * XXX this is cheating, should use continuations.
 * XXX the malloc()ed string is leaked if we yield in here.
 * Caller is responsible to free().
 * Does UTF-8 encoding.
 */
struct bytestring
evalstring(NODEPTR n)
{
  size_t sz = 100;
  char *buf = mmalloc(sz);
  size_t offs;
  uvalue_t c;
  NODEPTR x;
  struct bytestring bs;

  for (offs = 0;;) {
    if (offs >= sz - 4) {
      sz *= 2;
      buf = mrealloc(buf, sz);
    }
    PUSH(n);                    /* protect the list from GC */
    n = evali(n);
    POP(1);
    if (GETTAG(n) == T_K)       /* Nil */
      break;
    else if (GETTAG(n) == T_AP && GETTAG(x = indir(&FUN(n))) == T_AP && GETTAG(indir(&FUN(x))) == T_O) { /* Cons */
      PUSH(n);                  /* protect from GC */
      c = evalint(ARG(x));
      n = POPTOP();
      if ((c & 0x1ff800) == 0xd800) {
        // c is a surrogate
        c = 0xfffd; // replacement character
      }
      if (c < 0x80) {
        buf[offs++] = (char)c;
      } else if (c < 0x800) {
        buf[offs++] = ((c >> 6 )       ) | 0xc0;
        buf[offs++] = ((c      ) & 0x3f) | 0x80;
      } else if (c < 0x10000) {
        buf[offs++] = ((c >> 12)       ) | 0xe0;
        buf[offs++] = ((c >> 6 ) & 0x3f) | 0x80;
        buf[offs++] = ((c      ) & 0x3f) | 0x80;
      } else if (c < 0x110000) {
        buf[offs++] = ((c >> 18)       ) | 0xf0;
        buf[offs++] = ((c >> 12) & 0x3f) | 0x80;
        buf[offs++] = ((c >> 6 ) & 0x3f) | 0x80;
        buf[offs++] = ((c      ) & 0x3f) | 0x80;
      } else {
	ERR("invalid char");
      }
      n = ARG(n);
    } else {
      ERR("evalstring not Nil/Cons");
    }
  }
  buf[offs] = 0;                /* in case we use it as a C string */
  bs.size = offs;
  bs.string = buf;
  return bs;
}

/* Does not do UTF-8 encoding */
struct bytestring
evalbytestring(NODEPTR n)
{
  size_t sz = 100;
  uint8_t *buf = mmalloc(sz);
  size_t offs;
  uvalue_t c;
  NODEPTR x;
  struct bytestring bs;

  for (offs = 0;;) {
    if (offs >= sz - 1) {
      sz *= 2;
      buf = mrealloc(buf, sz);
    }
    PUSH(n);                    /* protect list from GC */
    n = evali(n);
    POP(1);
    if (GETTAG(n) == T_K)       /* Nil */
      break;
    else if (GETTAG(n) == T_AP && GETTAG(x = indir(&FUN(n))) == T_AP && GETTAG(indir(&FUN(x))) == T_O) { /* Cons */
      PUSH(n);                  /* protect from GC */
      c = evalint(ARG(x));
      n = POPTOP();
      buf[offs++] = c;
      n = ARG(n);
    } else {
      //pp(stdout, n);
      ERR("evalbytestring not Nil/Cons");
    }
  }
  buf[offs] = 0;                /* in case we use it as a C string */
  bs.size = offs;
  bs.string = buf;
  return bs;
}

struct bytestring
bsreplicate(size_t size, uint8_t value)
{
  struct bytestring bs;
  bs.size = size;
  bs.string = mmalloc(size);
  memset(bs.string, value, size);
  return bs;
}

struct bytestring
bsappend(struct bytestring p, struct bytestring q)
{
  struct bytestring r;
  r.size = p.size + q.size;
  r.string = mmalloc(r.size);
  memcpy(r.string, p.string, p.size);
  memcpy((uint8_t *)r.string + p.size, q.string, q.size);
  return r;
}

struct bytestring
bsappenddot(struct bytestring p, struct bytestring q)
{
  struct bytestring r;
  r.size = p.size + q.size + 1;
  r.string = mmalloc(r.size);
  memcpy(r.string, p.string, p.size);
  memcpy((uint8_t *)r.string + p.size, ".", 1);
  memcpy((uint8_t *)r.string + p.size + 1, q.string, q.size);
  return r;
}

/*
 * Compare bytestrings.
 * We can't use memcmp() directly for two reasons:
 *  - the two strings can have different lengths
 *  - the return value is only guaranteed to be ==0 or !=0
 */
int
bscompare(struct bytestring bsp, struct bytestring bsq)
{
  uint8_t *p = bsp.string;
  uint8_t *q = bsq.string;
  size_t len = bsp.size < bsq.size ? bsp.size : bsq.size;
  while (len--) {
    int r = (int)*p++ - (int)*q++;
    if (r) {
      /* Unequal bytes found. */
      if (r < 0)
        return -1;
      if (r > 0)
        return 1;
      return 0;
    }
  }
  /* Got to the end of the shorter string. */
  /* The shorter string is considered smaller. */
  if (bsp.size < bsq.size)
    return -1;
  if (bsp.size > bsq.size)
    return 1;
  return 0;
}

/* Compares anything, but really only works well on strings.
 * if p < q  return -1
 * if p > q  return 1
 * if p == q return 0
 *
 * As we compare we update the argument pointers with any
 * progress we make, in case we are interruped and resume from the top.
 *
 * XXX This is a rather dodgy comparison, since we are comparing
 * functions, and the same data type could plausibly get different
 * functions in the Scott encoding.
 * But we only use it for lists, and it seems to work fine.
 */
int
compare(NODEPTR cmp)
{
  stackptr_t stk = stack_ptr;
#define CRET(x) do { stack_ptr = stk; return (x); } while(0)
  value_t x, y;
  flt_t xd, yd;
  void *f, *g;
  void (*ff)(void), (*fg)(void);
  NODEPTR p, q;
  NODEPTR *ap, *aq;
  enum node_tag ptag, qtag;
  int r;

  /* Since FUN(cmp) can be shared, allocate a copy for it. */
  GCCHECK(1);
  FUN(cmp) = new_ap(FUN(FUN(cmp)), ARG(FUN(cmp)));
  aq = &ARG(cmp);
  ap = &ARG(FUN(cmp));

  PUSH(*ap);
  PUSH(*aq);
  for(;;) {
    if (stk == stack_ptr)
      return 0;
    q = evali(TOP(0));
    p = evali(TOP(1));
    POP(2);
    if (stk == stack_ptr) {
      /* We have made some progress, save this in the compare node. */
      *ap = p;
      *aq = q;
    }

    ptag = GETTAG(p);
    qtag = GETTAG(q);
    if (ptag != qtag) {
      /* Hack to make Nil < Cons */
      if (ptag == T_K && qtag == T_AP)
        CRET(-1);
      if (ptag == T_AP && qtag == T_K)
        CRET(1);
      CRET(ptag < qtag ? -1 : 1);
    }
    switch (ptag) {
    case T_AP:
      PUSH(ARG(p));             /* compare arg part later */
      PUSH(ARG(q));
      PUSH(FUN(p));             /* compare fun part now */
      PUSH(FUN(q));
      break;
    case T_INT:
    case T_IO_CCALL:
    case T_THID:
      x = GETVALUE(p);
      y = GETVALUE(q);
      if (x < y)
        CRET(-1);
      if (x > y)
        CRET(1);
      break;
    case T_DBL:
      xd = GETDBLVALUE(p);
      yd = GETDBLVALUE(q);
      if (xd < yd)
        CRET(-1);
      if (xd > yd)
        CRET(1);
      break;
    case T_PTR:
      f = PTR(p);
      g = PTR(q);
      if (f < g)
        CRET(-1);
      if (f > g)
        CRET(1);
      break;
    case T_FUNPTR:
      ff = FUNPTR(p);
      fg = FUNPTR(q);
      if ((intptr_t)ff < (intptr_t)fg)
        CRET(-1);
      if ((intptr_t)ff > (intptr_t)fg)
        CRET(1);
      break;
    case T_FORPTR:
      {
      struct forptr *fp = FORPTR(p);
      struct forptr *fq = FORPTR(q);
#if WANT_GMP
      if (fp->finalizer->fptype == FP_MPZ && fq->finalizer->fptype == FP_MPZ) {
        int i = mpz_cmp(fp->payload.string, fq->payload.string);
        if (i < 0)
          CRET(-1);
        if (i > 0)
          CRET(1);
      } else
#endif
      if (fp->finalizer->fptype == FP_BSTR && fq->finalizer->fptype == FP_BSTR) {
        r = bscompare(BSTR(p), BSTR(q));
        if (r)
          CRET(r);
      } else {
        f = fp->payload.string;
        g = fq->payload.string;
        if (f < g)
          CRET(-1);
        if (f > g)
          CRET(1);
      }
      }
      break;
    case T_ARR:
      if (ARR(p) < ARR(q))
        CRET(-1);
      if (ARR(p) > ARR(q))
        CRET(1);
      break;
    default:
      break;
    }
  }
#undef CRET
}

void
rnf_rec(bits_t *done, NODEPTR n)
{
 top:
  if (test_bit(done, n))
    return;
  set_bit(done, n);
  n = evali(n);
  if (GETTAG(n) == T_AP) {
    PUSH(ARG(n));               /* protect from GC */
    rnf_rec(done, FUN(n));
    n = POPTOP();
    goto top;
  }
}

void
rnf(value_t noerr, NODEPTR n)
{
  /* Mark visited nodes to avoid getting stuck in loops. */
  bits_t *done = mcalloc(free_map_nwords, sizeof(bits_t));
  if (doing_rnf)
    ERR("recursive rnf()");
  doing_rnf = (int)noerr;
  rnf_rec(done, n);
  doing_rnf = 0;
  FREE(done);
}

/* Evaluate a node, returns when the node is in WHNF. */
NODEPTR
evali(NODEPTR an)
{
  NODEPTR n = an;
  stackptr_t stk = stack_ptr;
  NODEPTR x, y, z, w;
  value_t xi, yi, r;
  struct forptr *xfp;
#if WANT_FLOAT
  flt_t xd, rd;
#endif  /* WANT_FLOAT */
  char *msg;
  heapoffs_t l;
  enum node_tag tag;
  struct ioarray *arr;
  struct bytestring xbs, ybs, rbs;
#if WANT_STDIO
  void *bfile;
  int hdr;
#endif  /* WANT_STDIO */

#if MAXSTACKDEPTH
  counter_t old_cur_c_stack = cur_c_stack;
  if (++cur_c_stack > max_c_stack)
    max_c_stack = cur_c_stack;
#endif

/* Reset stack pointer and return. */
#define RET do { goto ret; } while(0)
#define HASNARGS(n) (stack_ptr - stk >= (n))
/* Check that there are at least n arguments, return if not. */
#define CHECK(n) do { if (!HASNARGS(n)) RET; } while(0)

#define SETIND(n, x) SETINDIR(n, x)
#define GOIND(x) do { NODEPTR _x = (x); SETIND(n, _x); n = _x; goto top; } while(0)
#define GOAP(f,a) do { FUN(n) = (f); ARG(n) = (a); goto ap; } while(0)
#define GOAP2(f,a,b) do { FUN(n) = new_ap((f), (a)); ARG(n) = (b); goto ap2; } while(0)
#define GOPAIR(a) do { FUN(n) = new_ap(combPair, (a)); goto ap; } while(0)
#define GOPAIRUNIT do { FUN(n) = combPairUnit; goto ap; } while(0)
/* CHKARGN checks that there are at least N arguments.
 * It also
 *  - sets n to the "top" node
 *  - set x, y, ... to the arguments
 *  - pops N stack elements
 * NOTE: No GC is allowed after these, since the stack has been popped.
 */
#define CHKARG0 do { } while(0)
#define CHKARG1 do { CHECK(1); POP(1); n = TOP(-1); x = ARG(n); } while(0)
#define CHKARG2 do { CHECK(2); POP(2); n = TOP(-1); y = ARG(n); x = ARG(TOP(-2)); } while(0)
#define CHKARG3 do { CHECK(3); POP(3); n = TOP(-1); z = ARG(n); y = ARG(TOP(-2)); x = ARG(TOP(-3)); } while(0)
#define CHKARG4 do { CHECK(4); POP(4); n = TOP(-1); w = ARG(n); z = ARG(TOP(-2)); y = ARG(TOP(-3)); x = ARG(TOP(-4)); } while(0)
#define CHKARG5 do { CHECK(5); POP(5); n = TOP(-1); /*v = ARG(n);*/ w = ARG(TOP(-2)); z = ARG(TOP(-3)); y = ARG(TOP(-4)); x = ARG(TOP(-5)); } while(0)
/* Non-popping versions */
#define CHKARG1NP do { CHECK(1); n = TOP(0);                                               x = ARG(n);      } while(0)
#define CHKARG2NP do { CHECK(2); n = TOP(1);                              y = ARG(n);      x = ARG(TOP(0)); } while(0)
#define CHKARG3NP do { CHECK(3); n = TOP(2);             z = ARG(n);      y = ARG(TOP(1)); x = ARG(TOP(0)); } while(0)
#define CHKARG4NP do { CHECK(4); n = TOP(3); w = ARG(n); z = ARG(TOP(2)); y = ARG(TOP(1)); x = ARG(TOP(0)); } while(0)

/* Alloc a possible GC action, e, between setting x and popping */
#define CHKARGEV1(e)   do { CHECK(1); x = ARG(TOP(0)); e; POP(1); n = TOP(-1); } while(0)

#define SETINT(n,r)    do { SETTAG((n), T_INT); SETVALUE((n), (r)); } while(0)
#define SETDBL(n,d)    do { SETTAG((n), T_DBL); SETDBLVALUE((n), (d)); } while(0)
#define SETPTR(n,r)    do { SETTAG((n), T_PTR); PTR(n) = (r); } while(0)
#define SETFUNPTR(n,r) do { SETTAG((n), T_FUNPTR); FUNPTR(n) = (r); } while(0)
#define SETFORPTR(n,r) do { SETTAG((n), T_FORPTR); FORPTR(n) = (r); } while(0)
#define SETBSTR(n,r)   do { SETTAG((n), T_FORPTR); FORPTR(n) = (r); FORPTR(n)->finalizer->fptype = FP_BSTR; } while(0)
#define OPINT1(e)      do { CHECK(1); xi = evalint(ARG(TOP(0)));                            e; POP(1); n = TOP(-1); } while(0);
#define OPPTR2(e)      do { CHECK(2); xp = evalptr(ARG(TOP(0))); yp = evalptr(ARG(TOP(1))); e; POP(2); n = TOP(-1); } while(0);
#define CMPP(op)       do { OPPTR2(r = xp op yp); GOIND(r ? combTrue : combFalse); } while(0)

 top:
  /*pp(stdout, an);*/
  if (--glob_slice <= 0)
    yield();
  l = LABEL(n);
  if (l < T_IO_STDIN) {
    /* The node is one of the permanent nodes; the address offset is the tag */
    tag = l;
  } else {
    /* Heap allocated node */
    if (ISINDIR(n)) {
      /* Follow indirections */
      NODEPTR on = n;
      do {
        n = GETINDIR(n);
      } while(ISINDIR(n));
      SETINDIR(on, n);          /* and short-circuit them */
    }
    tag = GETTAG(n);
  }
  //COUNT(num_reductions);
  //printf("%s %d\n", tag_names[tag], (int)stack_ptr);
  //if (stack_ptr < -1)
  //  ERR("stack_ptr");
  switch (tag) {
  ap2:         PUSH(n); n = FUN(n);
  ap:
  case T_AP:   PUSH(n);
    n = FUN(n); goto top;

  case T_INT:    RET;
  case T_DBL:    RET;
  case T_PTR:    RET;
  case T_FUNPTR: RET;
  case T_FORPTR: RET;
  case T_ARR:    RET;
  case T_THID:   RET;
  case T_MVAR:   RET;
  case T_BADDYN: ERR1("FFI unknown %s", CSTR(n));

  /*
   * Some of these reductions, (e.g., Z x y = K (x y)) are there to avoid
   * that increase in arity that some "optimizations" in Abstract.hs
   * stop reductions from happening.  This can be important for "full laziness".
   * In practice, these reductions almost never happen, but there they are anyway. :)
   */
  case T_S:    GCCHECK(2); CHKARG3; GOAP2(x, z, new_ap(y, z));                            /* S x y z = x z (y z) */
  case T_SS:   GCCHECK(3); CHKARG4; GOAP2(x, new_ap(y, w), new_ap(z, w));                 /* S' x y z w = x (y w) (z w) */
  case T_K:                CHKARG2; GOIND(x);                                             /* K x y = *x */
  case T_A:                CHKARG2; GOIND(y);                                             /* A x y = *y */
  case T_U:                CHKARG2; GOAP(y, x);                                           /* U x y = y x */
  case T_I:                CHKARG1; GOIND(x);                                             /* I x = *x */
  case T_Y:                CHKARG1; GOAP(x, n);                                           /* n@(Y x) = x n */
  case T_B:    GCCHECK(1); CHKARG3; GOAP(x, new_ap(y, z));                                /* B x y z = x (y z) */
  case T_BB:   if (!HASNARGS(4)) {
               GCCHECK(1); CHKARG2; COUNT(red_bb); GOAP(combB, new_ap(x, y)); } else {    /* B' x y = B (x y) */
               GCCHECK(2); CHKARG4; GOAP2(x, y, new_ap(z, w)); }                          /* B' x y z w = x y (z w) */
  case T_Z:    if (!HASNARGS(3)) {
               GCCHECK(1); CHKARG2; COUNT(red_z); GOAP(combK, new_ap(x, y)); } else {     /* Z x y = K (x y) */
                           CHKARG3; GOAP(x, y); }                                         /* Z x y z = x y */
//case T_J:                CHKARG3; GOAP(z, x);                                           /* J x y z = z x */
  t_c:
  case T_C:    GCCHECK(1); CHKARG3; GOAP2(x, z, y);                                       /* C x y z = x z y */
  case T_CC:   GCCHECK(2); CHKARG4; GOAP2(x, new_ap(y, w), z);                            /* C' x y z w = x (y w) z */
  t_p:
  case T_P:    GCCHECK(1); CHKARG3; GOAP2(z, x, y);                                       /* P x y z = z x y */
  case T_R:    if(!HASNARGS(3)) {
               GCCHECK(1); CHKARG2; COUNT(red_r); GOAP2(combC, y, x); } else {            /* R x y = C y x */
               GCCHECK(1); CHKARG3; GOAP2(y, z, x); }                                     /* R x y z = y z x */
  case T_O:    GCCHECK(1); CHKARG4; GOAP2(w, x, y);                                       /* O x y z w = w x y */
  case T_K2:   if (!HASNARGS(3)) {
                           CHKARG2; COUNT(red_k2); GOAP(combK, x); } else {               /* K2 x y = K x */
                           CHKARG3; GOIND(x); }                                           /* K2 x y z = *x */
  case T_K3:   if (!HASNARGS(4)) {
                           CHKARG2; COUNT(red_k3); GOAP(combK2, x); } else {              /* K3 x y = K2 x */
                           CHKARG4; GOIND(x); }                                           /* K3 x y z w = *x */
  case T_K4:   if (!HASNARGS(5)) {
                           CHKARG2; COUNT(red_k4); GOAP(combK3, x); } else {              /* K4 x y = K3 x */
                           CHKARG5; GOIND(x); }                                           /* K4 x y z w v = *x */
  case T_CCB:  if (!HASNARGS(4)) {
               GCCHECK(2); CHKARG3; COUNT(red_ccb); GOAP2(combB, new_ap(x, z), y);} else{ /* C'B x y z = B (x z) y */
               GCCHECK(2); CHKARG4; GOAP2(x, z, new_ap(y, w)); }                          /* C'B x y z w = x z (y w) */

    /*
     * Strict primitives require evaluating the arguments before we can proceed.
     * The easiest way to do this is to just recursively call evali() for each argument.
     * The drawback of this is that it uses a lot of C stack.  (E.g., recompiling MicroHs
     * uses a stack depth of 1800).
     * Instead we use the following scheme:
     *  When we find a strict binary (int) primitive we push T_BININT2,
     *  set n=second argument.
     *  Continue evaluation of n.
     *  When n is finally evaluated and we are about to return we check if the stack top is T_BININT2.
     *  If so, change the stack top to T_BININT1,
     *  set n=first argument.
     *  Continue evaluation of n.
     *  When n is finally evaluated and we are about to return we check if the stack top is T_BININT1.
     *  If so, we know that both arguments are now evaluated, and we perform the strict operation.
     *
     * On my desktop machine this is about 3% slower, on my laptop (Apple M1) it is about 3% faster.
     *
     * Pictorially for BININT
     *  Before the code below:
     *  ----
     *  | --------> @
     *  ----       / \
     *  | ------> @   y
     *  ----     / \
     *  n ----> ADD x
     *
     * After
     *  ----
     *  | --------> @
     *  ----       / \
     *  | ------> @   y
     *  ----     / \
     *  | ->BI2 ADD x
     *  ----        ^
     *  n ----------|
     *
     *  x becomes an INT, stack is not empty, BININT2 found on top
     *  ----
     *  | --------> @
     *  ----       / \
     *  | ------> @   y
     *  ----     / \
     *  | ->BI2 ADD INT
     *  ----        ^
     *  n ----------|
     *
     *  After
     *  ----
     *  | --------> @
     *  ----       / \
     *  | ------> @   y
     *  ----     / \    \
     *  | ->BI1 ADD INT  |
     *  ----             |
     *  n ---------------|
     *
     *  y becomes an INT, stack is not empty, BININT1 found on top
     *  do arithmetic
     *  ----
     *  | --------> @
     *  ----       / \
     *  | ------> @   INT
     *  ----     / \    \
     *  | ->BI1 ADD INT  |
     *  ----             |
     *  n ---------------|
     *
     *  ----
     *  n -------> INT(x+y)
     */
  case T_ADD:
  case T_SUB:
  case T_MUL:
  case T_QUOT:
  case T_REM:
  case T_SUBR:
  case T_UQUOT:
  case T_UREM:
  case T_AND:
  case T_OR:
  case T_XOR:
  case T_SHL:
  case T_SHR:
  case T_ASHR:
  case T_EQ:
  case T_NE:
  case T_LT:
  case T_LE:
  case T_GT:
  case T_GE:
  case T_ICMP:
  case T_ULT:
  case T_ULE:
  case T_UGT:
  case T_UGE:
  case T_UCMP:
    CHECK(2);
    n = ARG(TOP(1));
    if (GETTAG(n) == T_INT) {
      n = ARG(TOP(0));
      PUSH(combBININT1);
      if (GETTAG(n) == T_INT)
        goto binint1;
    } else {
      PUSH(combBININT2);
    }
    goto top;
  case T_NEG:
  case T_INV:
  case T_POPCOUNT:
  case T_CLZ:
  case T_CTZ:
    CHECK(1);
    n = ARG(TOP(0));
    PUSH(combUNINT1);
    goto top;

#if WANT_FLOAT
  case T_FADD:
  case T_FSUB:
  case T_FMUL:
  case T_FDIV:
  case T_FEQ:
  case T_FNE:
  case T_FLT:
  case T_FLE:
  case T_FGT:
  case T_FGE:
    CHECK(2);
    n = ARG(TOP(1));
    PUSH(combBINDBL2);
    goto top;
  case T_FNEG:
    CHECK(1);
    n = ARG(TOP(0));
    PUSH(combUNDBL1);
    goto top;

  case T_ITOF: OPINT1(rd = (flt_t)xi); SETDBL(n, rd); RET;
  case T_FREAD:
    CHECK(1);
    msg = evalstring(ARG(TOP(0))).string;
#if WORD_SIZE == 64
    xd = strtod(msg, NULL);
#elif WORD_SIZE == 32
    xd = strtof(msg, NULL);
#else  /* WORD_SIZE */
#error Unknown WORD_SIZE
#endif  /* WORD_SIZE */
    FREE(msg);
    POP(1);
    n = TOP(-1);
    SETDBL(n, xd);
    RET;

  case T_FSHOW:
    CHECK(1);
    xd = evaldbl(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    GOIND(dblToString(xd));
#endif  /* WANT_FLOAT */

  case T_ISINT:
    CHECK(1);
    x = evali(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETINT(n, GETTAG(x) == T_INT ? GETVALUE(x) : -1);
    RET;

  case T_BSAPPEND:
  case T_BSAPPENDDOT:
  case T_BSEQ:
  case T_BSNE:
  case T_BSLT:
  case T_BSLE:
  case T_BSGT:
  case T_BSGE:
  case T_BSCMP:
    CHECK(2);
    n = ARG(TOP(1));
    PUSH(combBINBS2);
    goto top;

  /* Retag a word sized value, keeping the value bits */
#define CONV(t) do { CHECK(1); x = evali(ARG(TOP(0))); n = POPTOP(); SETTAG(n, t); SETVALUE(n, GETVALUE(x)); RET; } while(0)
  case T_TODBL: CONV(T_DBL);
  case T_TOINT: CONV(T_INT);
  case T_TOPTR: CONV(T_PTR);
  case T_TOFUNPTR: CONV(T_FUNPTR);
#undef CONV

  case T_FPADD: CHECK(2); xfp = evalforptr(ARG(TOP(0))); yi = evalint(ARG(TOP(1))); POP(2); n = TOP(-1); SETFORPTR(n, addForPtr(xfp, yi)); RET;
  case T_FP2P:
    CHECK(1);
    xfp = evalforptr(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETPTR(n, xfp->payload.string);
    RET;

  case T_FP2BS:
    CHECK(2);
    xfp = evalforptr(ARG(TOP(0)));
    xi = evalint(ARG(TOP(1)));
    POP(2);
    n = TOP(-1);
    xfp->payload.size = xi;
    SETBSTR(n, xfp);
    RET;

  case T_BS2FP:
    CHECK(1);
    xfp = evalbstr(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETFORPTR(n, xfp);
    RET;

  case T_ARR_EQ:
    {
      CHECK(2);
      x = evali(ARG(TOP(0)));
      arr = ARR(x);
      y = evali(ARG(TOP(1)));
      POP(2);
      n = TOP(-1);
      GOIND(arr == ARR(y) ? combTrue : combFalse);
    }

  case T_BSTOUTF8:
    {
      CHECK(1);
      n = ARG(TOP(0));
      /* Zap the pointer to the list so it can be GC:ed.
       * The actual list is protected from GC by evalbytestring().
       */
      // ARG(TOP(0)) = combK;
      struct bytestring bs = evalstring(n);
      POP(1);
      n = TOP(-1);
      SETBSTR(n, mkForPtrFree(bs));
      RET;
    }

  case T_BSHEADUTF8:
    CHECK(1);
    xfp = evalbstr(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETINT(n, headutf8(xfp->payload, (void**)0));
    RET;

  case T_BSTAILUTF8:
    CHECK(1);
    xfp = evalbstr(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    { void *out;
      (void)headutf8(xfp->payload, &out);           /* skip one UTF8 character */
      xi = (char*)out - (char*)xfp->payload.string; /* offset */
      yi = xfp->payload.size - xi;                  /* remaining length */
      SETBSTR(n, bssubstr(xfp, xi, yi));            /* make a substring */
    }
    RET;

  case T_BSFROMUTF8:
    if (doing_rnf) RET;
    CHECK(1);

    xfp = evalbstr(ARG(TOP(0)));
    GCCHECK(strNodes(xfp->payload.size));
    POP(1);
    n = TOP(-1);
    //printf("T_FROMUTF8 x = %p fp=%p payload.string=%p\n", x, x->uarg.uuforptr, x->uarg.uuforptr->payload.string);
    GOIND(mkStringU(xfp->payload));

  case T_BSUNPACK:
    if (doing_rnf) RET;
    CHECK(1);
    struct forptr *xfp = evalbstr(ARG(TOP(0)));
    GCCHECK(strNodes(xfp->payload.size));
    POP(1);
    n = TOP(-1);
    GOIND(bsunpack(xfp->payload));

  case T_BSPACK:
    CHECK(1);
    n = ARG(TOP(0));
    /* Zap the pointer to the list so it can be GC:ed.
     * The actual list is protected from GC by evalbytestring().
     */
    ARG(TOP(0)) = combK;
    struct bytestring rbs = evalbytestring(n);
    POP(1);
    n = TOP(-1);
    SETBSTR(n, mkForPtrFree(rbs));
    RET;

  case T_BSREPLICATE:
    CHECK(2);
    xi = evalint(ARG(TOP(0)));
    yi = evalint(ARG(TOP(1)));
    POP(2);
    n = TOP(-1);
    SETBSTR(n, mkForPtrFree(bsreplicate(xi, yi)));
    RET;

  case T_BSLENGTH:
    CHECK(1);
    xfp = evalbstr(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETINT(n, xfp->payload.size);
    RET;

  case T_BSSUBSTR:
    CHECK(3);
    xfp = evalbstr(ARG(TOP(0)));
    xi = evalint(ARG(TOP(1)));
    yi = evalint(ARG(TOP(2)));
    POP(3);
    n = TOP(-1);
    SETBSTR(n, bssubstr(xfp, xi, yi));
    RET;

  case T_BSINDEX:
    CHECK(2);
    xfp = evalbstr(ARG(TOP(0)));
    xi = evalint(ARG(TOP(1)));
    POP(2);
    n = TOP(-1);
    SETINT(n, ((uint8_t *)xfp->payload.string)[xi]);
    RET;

  case T_RAISE:
    if (doing_rnf) RET;
    CHKARG1;
    raise_exn(x);               /* never returns */
    

  case T_SEQ:  CHECK(2); evali(ARG(TOP(0))); POP(2); n = TOP(-1); y = ARG(n); GOIND(y); /* seq x y = eval(x); y */

  case T_EQUAL:
    CHECK(2); r = compare(TOP(1)); POP(2); n = TOP(-1); GOIND(r==0 ? combTrue : combFalse);
  case T_COMPARE:
    CHECK(2); r = compare(TOP(1)); POP(2); n = TOP(-1); GOIND(r < 0 ? combLT : r > 0 ? combGT : combEQ);

  case T_RNF:
    if (doing_rnf) RET;
    CHECK(2);
    xi = evalint(ARG(TOP(0)));
    rnf(xi, ARG(TOP(1))); POP(2); n = TOP(-1); GOIND(combUnit);

  case T_IO_PERFORMIO:
    GCCHECK(2);
    if (doing_rnf) RET;
    CHKARG1;
    /* Conjure up a new world and evaluate the io with that world, finally selecting the result */
    /* PERFORMIO io  -->  io World K */
    GOAP2(x, combWorld, combK);

  case T_IO_BIND:
    goto t_c;
  case T_IO_RETURN:
    goto t_p;
  case T_IO_THEN:
    GCCHECK(2); CHKARG2; GOAP2(combIOBIND, x, new_ap(combK, y));
#if WANT_STDIO
  case T_IO_PP:
    CHKARG2;
    pp(stderr, x);
    GOPAIRUNIT;
  case T_IO_PRINT:
    hdr = 0;
    goto ser;
  case T_IO_SERIALIZE:
    hdr = 1;
  ser:
#if 0
    gc();                     /* DUBIOUS: do a GC to get possible GC reductions */
#endif
    CHKARG3NP;
    bfile = (struct BFILE*)evalptr(x);
    printb(bfile, evali(y), hdr);
    putb('\n', bfile);
    POP(3);
    GOPAIRUNIT;
  case T_IO_DESERIALIZE:
    CHKARG2NP;
    bfile = (struct BFILE*)evalptr(x);
    gc();                     /* make sure we have room.  GC during parse is dodgy. */
    x = parse_top(bfile);
    POP(2);
    GOPAIR(x);                /* allocates a cell, but we did a GC above */
#endif
#if WANT_ARGS
  case T_IO_GETARGREF:
    GCCHECK(2);
    CHKARG1;
    x = alloc_node(T_ARR);
    ARR(x) = argarray;
    GOPAIR(x);
#endif
  case T_IO_CCALL:
    {
      GCCHECK(1);                 /* room for placeholder */
      int a = (int)GETVALUE(n);   /* function number */
      int arity = FFI_IX(a).ffi_arity;
      CHECK(arity);
      funptr_t f = FFI_IX(a).ffi_fun;
      PUSH(mkFlt(0.0));           /* placeholder for result, protected from GC */
      int k = f(stk);             /* call FFI function, return number of arguments */
      if (k != arity) {
#if WANT_STDIO
        fprintf(stderr, "ccall arity %s %d!=%d\n", FFI_IX(a).ffi_name, arity, k);
#endif
        ERR("ccall arity");     /* temporary sanity check */
      }
      GCCHECK(1);                 /* room for pair */
      x = POPTOP();               /* pop actual result */
      POP(arity);                 /* pop the pushed arguments */
      if (stack_ptr < 0)
        ERR("CCALL POP");
      n = POPTOP();               /* node to update */
      GOPAIR(x);                  /* and this is the result */
    }

  case T_NEWCASTRINGLEN:
    {
      CHKARG2NP;                /* set x,y,n */
      struct bytestring bs = evalbytestring(x);
      GCCHECK(5);
      NODEPTR cs = alloc_node(T_PTR);
      PTR(cs) = bs.string;
      NODEPTR res = new_ap(new_ap(combPair, cs), mkInt(bs.size));
      POP(2);
      GOPAIR(res);
    }
  case T_PACKCSTRING:
    {
      CHKARG2NP;                  /* sets x, y, n */
      char *cstr = evalptr(x);
      size_t size = strlen(cstr);
      char *str = mmalloc(size);
      memcpy(str, cstr, size);
      struct bytestring bs = { size, str };
      NODEPTR res = mkStrNode(bs);
      GCCHECKSAVE(res, 1);
      POP(2);
      GOPAIR(res);
    }
  case T_PACKCSTRINGLEN:
    {
      CHKARG3NP;                /* sets x,y,z,n */
      char *cstr = evalptr(x);
      size_t size = evalint(y);
      char *str = mmalloc(size);
      memcpy(str, cstr, size);
      struct bytestring bs = { size, str };
      NODEPTR res = mkStrNode(bs);
      POP(3);
      GCCHECKSAVE(res, 1);
      GOPAIR(res);
    }

  case T_ARR_ALLOC:
    {
      CHKARG3NP;                /* sets x,y,z,n */
      size_t size = evalint(x);
      struct ioarray *arr = arr_alloc(size, y);
      GCCHECK(2);
      NODEPTR res = alloc_node(T_ARR);
      ARR(res) = arr;
      POP(3);
      GOPAIR(res);
    }
  case T_ARR_COPY:
    {
      CHKARG2NP;
      NODEPTR a = evali(x);
      if (GETTAG(a) != T_ARR)
        ERR("T_ARR_COPY tag");
      struct ioarray *arr = arr_copy(ARR(a));
      GCCHECK(2);
      NODEPTR res = alloc_node(T_ARR);
      ARR(res) = arr;
      POP(2);
      GOPAIR(res);
    }
  case T_ARR_SIZE:
    {
      CHKARG2NP;
      NODEPTR a = evali(x);
      if (GETTAG(a) != T_ARR)
        ERR("bad ARR tag");
      GCCHECK(2);
      NODEPTR res = mkInt(ARR(a)->size);
      POP(2);
      GOPAIR(res);
    }
  case T_ARR_READ:
    {
      CHKARG3NP;                /* sets x,y,n */
      size_t i = evalint(y);
      NODEPTR a = evali(x);
      if (GETTAG(a) != T_ARR)
        ERR("bad ARR tag");
      if (i >= ARR(a)->size)
        ERR("ARR_READ");
      GCCHECK(1);
      NODEPTR res = ARR(a)->array[i];
      POP(3);
      GOPAIR(res);
    }
  case T_ARR_WRITE:
    {
      CHKARG4NP;                /* sets x,y,z,n */
      size_t i = evalint(y);
      NODEPTR a = evali(x);
      if (GETTAG(a) != T_ARR)
        ERR("bad ARR tag");
      if (i >= ARR(a)->size) {
        ERR("ARR_WRITE");
      }
      ARR(a)->array[i] = z;
      POP(4);
      GOPAIRUNIT;
      }

  case T_FPNEW:
    {
      CHKARG2NP;
      //printf("T_FPNEW\n");
      void *xp = evalptr(x);
      //printf("T_FPNEW xp=%p\n", xp);
      GCCHECK(2);
      NODEPTR res = alloc_node(T_FORPTR);
      SETFORPTR(res, mkForPtrP(xp));
      POP(2);
      GOPAIR(res);
    }
  case T_FPFIN:
    {
      CHKARG3NP;
      //printf("T_FPFIN\n");
      struct forptr *xfp = evalforptr(y);
      //printf("T_FPFIN xfp=%p\n", xfp);
      HsFunPtr xp = evalfunptr(x);
      //printf("T_FPFIN yp=%p\n", yp);
      xfp->finalizer->final = xp;
      POP(3);
      GOPAIRUNIT;
    }
  case T_IO_GC:
    //printf("gc()\n");
    CHKARG1;
    gc();
    GOPAIRUNIT;

  case T_IO_STATS:
    {
    GCCHECK(4);
    CHKARG1;
    NODEPTR res = new_ap(new_ap(combPair, mkInt((uvalue_t)num_alloc)), mkInt((uvalue_t)(num_reductions - glob_slice)));
    GOPAIR(res);
    }

  case T_IO_FORK:
    {
      GCCHECK(3);
      CHKARG2;                /* set x=io, y=ST, n */
      struct mthread *mt = new_thread(new_ap(x, y)); /* copy the world */
      mt->mt_mask = runq.mq_head->mt_mask; /* inherit masking state */
      NODEPTR res = alloc_node(T_THID);
      THR(res) = mt;
      GOPAIR(res);
    }

  case T_IO_THID:
    {
      GCCHECK(2);
      CHKARG1;
      NODEPTR res = alloc_node(T_THID);
      THR(res) = runq.mq_head;            /* head of the run queue is the current thread */
      GOPAIR(res);
    }
  case T_IO_THROWTO:
    {
      CHKARG3NP;                /* x=this, y=exn, z=ST */
      struct mthread *mt = evalthid(x);
      throwto(mt, y);
      POP(3);
      GOPAIRUNIT;
    }
  case T_IO_YIELD:
    CHKARG1;
    yield();
    GOPAIRUNIT;

  case T_IO_NEWMVAR:
    {
      GCCHECK(2);
      CHKARG1;
      struct mvar *mv = new_mvar();
      NODEPTR res = alloc_node(T_MVAR);
      MVAR(res) = mv;
      GOPAIR(res);
    }
  case T_IO_TAKEMVAR:
    {
      CHKARG2NP;             /* set x=mvar, y=ST */
      check_thrown();        /* check if we have a thrown exception */
      NODEPTR res = take_mvar(0, evalmvar(x));         /* never returns if it blocks */
      GCCHECKSAVE(res, 1);
      POP(2);
      GOPAIR(res);
    }
  case T_IO_READMVAR:
    {
      CHKARG2NP;
      check_thrown();           /* check if we have a thrown exception */
      NODEPTR res = read_mvar(0, evalmvar(x));         /* never returns if it blocks */
      GCCHECKSAVE(res, 1);
      POP(2);
      GOPAIR(res);
    }
  case T_IO_PUTMVAR:
    {
      CHKARG3NP;             /* set x=mvar, y=value, z=ST */
      check_thrown();        /* check if we have a thrown exception */
      (void)put_mvar(0, evalmvar(x), y); /* never returns if it blocks */
      POP(3);
      GOPAIRUNIT;
    }
  case T_IO_TRYTAKEMVAR:
    {
      CHKARG2NP;
      NODEPTR res = take_mvar(1, evalmvar(x));
      GCCHECKSAVE(res, 2);
      if (res != NIL)
        res = new_ap(combJust, res);
      else
        res = combNothing;
      POP(2);
      GOPAIR(res);
    }
  case T_IO_TRYREADMVAR:
    {
      CHKARG2NP;
      NODEPTR res = read_mvar(1, evalmvar(x));
      if (res != NIL) {
        GCCHECKSAVE(res, 2);
        res = new_ap(combJust, res);
      } else {
        res = combNothing;
      }
      POP(2);
      GOPAIR(res);
    }
  case T_IO_TRYPUTMVAR:
    {
      CHKARG3NP;
      NODEPTR res = put_mvar(1, evalmvar(x), y) ? combTrue : combFalse;
      GCCHECKSAVE(res, 1);
      POP(3);
      GOPAIR(res);
    }
  case T_IO_THREADDELAY:
    {
      CHKARG2NP;
#if defined(CLOCK_INIT)
      check_thrown();           /* check if we have a thrown exception */
      if (runq.mq_head->mt_at == -1) {
        /* delay has already expired, so just return */
        runq.mq_head->mt_at = 0;
        POP(2);
        GOPAIRUNIT;
      } else {
        thread_delay(evalint(x)); /* never returns */
      }
#else
      ERR("threadDelay: no clock");
#endif
    }
  case T_IO_THREADSTATUS:
    {
      CHKARG2NP;
      struct mthread *mt = evalthid(x);
      GCCHECK(2);
      POP(2);
      GOPAIR(mkInt(mt->mt_state));
    }
  case T_IO_GETMASKINGSTATE:
    CHKARG1;                    /* x = ST */
    GOPAIR(mkInt(runq.mq_head->mt_mask));

  case T_IO_SETMASKINGSTATE:
    CHKARG2;                    /* x = level, y = ST */
    runq.mq_head->mt_mask = evalint(x);
    GOPAIRUNIT;

  case T_CATCH:
    /* CATCH x y z --> CATCHR (x z) y z */
    GCCHECK(3);
    CHKARG3;                    /* x=io, y=hdl, z=ST */
    GOAP(new_ap(new_ap(combCATCHR, new_ap(x, z)), y), z);
  case T_CATCHR:
    {
      CHKARG3NP;                /* x = (io st), y = hdl, z = st, n = (CATCHR (io st)) h */
      struct handler *h = mmalloc(sizeof *h);
      h->hdl_old = cur_handler;
      cur_handler = h;
      stackptr_t ostack = stack_ptr;;    /* old stack pointer */
      enum mask_state omask = runq.mq_head->mt_mask;     /* old mask */
      if (setjmp(h->hdl_buf)) {
        /* An exception occurred: */
        stack_ptr = ostack;
        runq.mq_head->mt_mask = mask_interruptible; /* evaluate with mask */
        NODEPTR exn = h->hdl_exn;       /* exception value */
        cur_handler = h->hdl_old;       /* reset handler */
        FREE(h);
        GCCHECK(8);
        POP(3);
        /*
         * Run:
         *  hdl exn `primBind` \ r ->
         *  primSetMaskingState omask `primThen`
         *  primReturn r
         * i.e.,
         *  primBind (hdl exn) (B' primThen (primSetMaskingState omask) primReturn)
         */
        NODEPTR p = new_ap(combIOBIND, new_ap(y, exn));
        NODEPTR q = new_ap(new_ap(new_ap(combBB, combIOTHEN), new_ap(combSETMASKINGSTATE, mkInt(omask))), combIORETURN);
        GOAP2(p, q, z);
      } else {
        /* Normal execution: */
        x = evali(x);             /* execute first argument */
        /* No exception occurred */
        cur_handler = h->hdl_old; /* restore old handler */
        FREE(h);
        POP(3);
        GOIND(x);
      }
    }

  case T_THNUM:
    {
    CHECK(1);
    struct mthread *mt = evalthid(ARG(TOP(0)));
    POP(1);
    n = TOP(-1);
    SETINT(n, (uvalue_t)mt->mt_id);
    RET;
    }

  case T_DYNSYM:
    /* A dynamic FFI lookup */
    CHECK(1);
    msg = evalstring(ARG(TOP(0))).string;
    GCCHECK(1);
    x = ffiNode(msg);
    FREE(msg);
    POP(1);
    n = TOP(-1);
    GOIND(x);

#if WANT_TICK
  case T_TICK:
    xi = GETVALUE(n);
    CHKARG1;
    dotick(xi);
    GOIND(x);
#endif

  default:
    ERR1("eval tag %s", tag_names[GETTAG(n)]);
  }


 ret:
  if (stack_ptr != stk) {
    // In this case, n was an AP that got pushed and potentially
    // updated.
    uvalue_t xu, yu, ru;
#if WANT_FLOAT
    flt_t xd, yd, rd;
#endif  /* WANT_FLOAT */
    NODEPTR p;

    tag = GETTAG(TOP(0));
    switch (tag) {
    case T_BININT2:
      n = ARG(TOP(1));
      TOP(0) = combBININT1;
      goto top;

    case T_BININT1:
      /* First argument */
#if SANITY
      if (GETTAG(n) != T_INT)
        ERR("BININT 0");
#endif  /* SANITY */
    binint1:
      xu = (uvalue_t)GETVALUE(n);
      /* Second argument */
      y = ARG(TOP(2));
      while (GETTAG(y) == T_IND)
        y = GETINDIR(y);
#if SANITY
      if (GETTAG(y) != T_INT)
        ERR("BININT 1");
#endif  /* SANITY */
      yu = (uvalue_t)GETVALUE(y);
      p = FUN(TOP(1));
      POP(3);
      n = TOP(-1);
    binint:
      switch (GETTAG(p)) {
      case T_IND:   p = GETINDIR(p); goto binint;
      case T_ADD:   ru = xu + yu; break;
      case T_SUB:   ru = xu - yu; break;
      case T_MUL:   ru = xu * yu; break;
      case T_SUBR:  ru = yu - xu; break;
      case T_QUOT:  if (yu == 0)
                      raise_rts(exn_dividebyzero);
                    else
                      ru = (uvalue_t)((value_t)xu / (value_t)yu);
                    break;
      case T_REM:   if (yu == 0)
                      raise_rts(exn_dividebyzero);
                    else
                      ru = (uvalue_t)((value_t)xu % (value_t)yu);
                    break;
      case T_UQUOT: if (yu == 0)
                      raise_rts(exn_dividebyzero);
                    else
                      ru = xu / yu;
                    break;
      case T_UREM:  if (yu == 0)
                      raise_rts(exn_dividebyzero);
                    else
                      ru = xu % yu;
                    break;
      case T_AND:   ru = xu & yu; break;
      case T_OR:    ru = xu | yu; break;
      case T_XOR:   ru = xu ^ yu; break;
      case T_SHL:   ru = xu << yu; break;
      case T_SHR:   ru = xu >> yu; break;
      case T_ASHR:  ru = (uvalue_t)((value_t)xu >> yu); break;

      case T_EQ:    GOIND(xu == yu ? combTrue : combFalse);
      case T_NE:    GOIND(xu != yu ? combTrue : combFalse);
      case T_ULT:   GOIND(xu <  yu ? combTrue : combFalse);
      case T_ULE:   GOIND(xu <= yu ? combTrue : combFalse);
      case T_UGT:   GOIND(xu >  yu ? combTrue : combFalse);
      case T_UGE:   GOIND(xu >= yu ? combTrue : combFalse);
      case T_UCMP:  GOIND(xu <  yu ? combLT   : xu > yu ? combGT : combEQ);
      case T_LT:    GOIND((value_t)xu <  (value_t)yu ? combTrue : combFalse);
      case T_LE:    GOIND((value_t)xu <= (value_t)yu ? combTrue : combFalse);
      case T_GT:    GOIND((value_t)xu >  (value_t)yu ? combTrue : combFalse);
      case T_GE:    GOIND((value_t)xu >= (value_t)yu ? combTrue : combFalse);
      case T_ICMP:  GOIND((value_t)xu <  (value_t)yu ? combLT   : (value_t)xu > (value_t)yu ? combGT : combEQ);

      default:
        //fprintf(stderr, "tag=%d\n", GETTAG(FUN(TOP(0))));
        ERR("BININT");
      }
      SETINT(n, (value_t)ru);
      goto ret;

    case T_UNINT1:
      /* The argument */
#if SANITY
      if (GETTAG(n) != T_INT)
        ERR("UNINT 0");
#endif
      xu = (uvalue_t)GETVALUE(n);
      p = FUN(TOP(1));
      POP(2);
      n = TOP(-1);
    unint:
      switch (GETTAG(p)) {
      case T_IND:      p = GETINDIR(p); goto unint;
      case T_NEG:      ru = -xu; break;
      case T_INV:      ru = ~xu; break;
      case T_POPCOUNT: ru = POPCOUNT(xu); break;
      case T_CLZ:      ru = CLZ(xu); break;
      case T_CTZ:      ru = CTZ(xu); break;
      default:
        //fprintf(stderr, "tag=%d\n", GETTAG(FUN(TOP(0))));
        ERR("UNINT");
      }
      SETINT(n, (value_t)ru);
      goto ret;

#if WANT_FLOAT
    case T_BINDBL2:
      n = ARG(TOP(1));
      TOP(0) = combBINDBL1;
      goto top;

    case T_BINDBL1:
      /* First argument */
#if SANITY
      if (GETTAG(n) != T_DBL)
        ERR("BINDBL 0");
#endif  /* SANITY */
      xd = GETDBLVALUE(n);
      /* Second argument */
      y = ARG(TOP(2));
      while (GETTAG(y) == T_IND)
        y = GETINDIR(y);
#if SANITY
      if (GETTAG(y) != T_DBL)
        ERR("BINDBL 1");
#endif  /* SANITY */
      yd = GETDBLVALUE(y);
      p = FUN(TOP(1));
      POP(3);
      n = TOP(-1);
    bindbl:
      switch (GETTAG(p)) {
      case T_IND:   p = GETINDIR(p); goto bindbl;
      case T_FADD:  rd = xd + yd; break;
      case T_FSUB:  rd = xd - yd; break;
      case T_FMUL:  rd = xd * yd; break;
      case T_FDIV:  rd = xd / yd; break;

      case T_FEQ:   GOIND(xd == yd ? combTrue : combFalse);
      case T_FNE:   GOIND(xd != yd ? combTrue : combFalse);
      case T_FLT:   GOIND(xd <  yd ? combTrue : combFalse);
      case T_FLE:   GOIND(xd <= yd ? combTrue : combFalse);
      case T_FGT:   GOIND(xd >  yd ? combTrue : combFalse);
      case T_FGE:   GOIND(xd >= yd ? combTrue : combFalse);

      default:
        //fprintf(stderr, "tag=%d\n", GETTAG(FUN(TOP(0))));
        ERR("BINDBL");
      }
      SETDBL(n, rd);
      goto ret;

    case T_UNDBL1:
      /* The argument */
#if SANITY
      if (GETTAG(n) != T_DBL)
        ERR("UNDBL 0");
#endif
      xd = GETDBLVALUE(n);
      p = FUN(TOP(1));
      POP(2);
      n = TOP(-1);
    undbl:
      switch (GETTAG(p)) {
      case T_IND:   p = GETINDIR(p); goto undbl;
      case T_FNEG:  rd = -xd; break;
      default:
        //fprintf(stderr, "tag=%d\n", GETTAG(FUN(TOP(0))));
        ERR("UNDBL");
      }
      SETDBL(n, rd);
      goto ret;
#endif  /* WANT_FLOAT */

    case T_BINBS2:
      n = ARG(TOP(1));
      TOP(0) = combBINBS1;
      goto top;

    case T_BINBS1:
      /* First argument */
#if SANITY
      if (GETTAG(n) != T_FORPTR || FORPTR(n)->finalizer->fptype != FP_BSTR)
        ERR("BINBS 0");
#endif  /* SANITY */
      xbs = BSTR(n);
      /* Second argument */
      y = ARG(TOP(2));
      while (GETTAG(y) == T_IND)
        y = GETINDIR(y);
#if SANITY
      if (GETTAG(y) != T_FORPTR || FORPTR(y)->finalizer->fptype != FP_BSTR)
        ERR("BINBS 1");
#endif  /* SANITY */
      ybs = BSTR(y);
      p = FUN(TOP(1));
      POP(3);
      n = TOP(-1);
    binbs:
      switch (GETTAG(p)) {
      case T_IND:    p = GETINDIR(p); goto binbs;

      case T_BSAPPEND: rbs = bsappend(xbs, ybs); break;
      case T_BSAPPENDDOT: rbs = bsappenddot(xbs, ybs); break;
      case T_BSEQ:   GOIND(bscompare(xbs, ybs) == 0 ? combTrue : combFalse);
      case T_BSNE:   GOIND(bscompare(xbs, ybs) != 0 ? combTrue : combFalse);
      case T_BSLT:   GOIND(bscompare(xbs, ybs) <  0 ? combTrue : combFalse);
      case T_BSLE:   GOIND(bscompare(xbs, ybs) <= 0 ? combTrue : combFalse);
      case T_BSGT:   GOIND(bscompare(xbs, ybs) >  0 ? combTrue : combFalse);
      case T_BSGE:   GOIND(bscompare(xbs, ybs) >= 0 ? combTrue : combFalse);
      case T_BSCMP:  r = bscompare(xbs, ybs); GOIND(r < 0 ? combLT : r > 0 ? combGT : combEQ);

      default:
        //fprintf(stderr, "tag=%d\n", GETTAG(FUN(TOP(0))));
        ERR("BINBS");
      }
      SETBSTR(n, mkForPtrFree(rbs));
      goto ret;

    default:
      stack_ptr = stk;
      n = TOP(-1);
    }
  }
#if MAXSTACKDEPTH
  cur_c_stack = old_cur_c_stack; /* reset rather than counting down, in case of longjump */
#endif
  return n;
}

NORETURN void
die_exn(NODEPTR exn)
{
  /* No handler:
   * First convert the exception to a string by calling displaySomeException.
   * The display function compiles to combShowExn, so we need to build
   * (combShowExn exn) and evaluate it.
   */
  NODEPTR x;
  char *msg;

  if (in_raise) {
    ERR("recursive error");
    EXIT(1);
  }
  in_raise = 1;

  if (GETTAG(exn) == T_INT) {
    /* This is the special hack for RTS generated exception, represented by a T_INT */
    switch(GETVALUE(exn)) {
    case 0: msg = "stack overflow"; break;
    case 1: msg = "heap overflow"; break;
    case 2: msg = "thread killed"; break;
    case 3: msg = "user interrupt"; break;
    case 4: msg = "DivideByZero"; break;
    default: msg = "unknown"; break;
    }
  } else {
    /* just overwrite the top stack element, we don't need it */
    CLEARSTK();
    GCCHECK(1);
    PUSH(new_ap(combShowExn, exn));/* TOP(0) = (combShowExn exn) */
    x = evali(TOP(0));             /* evaluate it */
    msg = evalstring(x).string;    /* and convert to a C string */
    POP(1);
  }
#if WANT_STDIO
  /* A horrible hack until we get proper exceptions */
  if (strcmp(msg, "ExitSuccess") == 0) {
    EXIT(0);
  } else {
    fprintf(stderr, "\nmhs: uncaught exception: %s\n", msg);
    EXIT(1);
  }
#else  /* WANT_STDIO */
  ERR1("mhs error: %s", msg);
#endif  /* WANT_STDIO */
}

#if WANT_ARGS
heapoffs_t
memsize(const char *p)
{
  heapoffs_t n = atoi(p);
  while (isdigit(*p))
    p++;
  switch (*p) {
  case 'k': case 'K': n *= 1000; break;
  case 'm': case 'M': n *= 1000000; break;
  case 'g': case 'G': n *= 1000000000; break;
  default: break;
  }
  return n;
}
#endif

extern uint8_t *combexpr;
extern int combexprlen;

MAIN
{
  NODEPTR prog;
#if WANT_ARGS
  char *inname = 0;
  char **av;
  char *progname;
  char **gargv;
  int gargc;
  int inrts;
#if WANT_TICK
  int dump_ticks = 0;
#endif
#endif
#if WANT_STDIO
  char *outname = 0;
  size_t file_size = 0;
#endif

#if 0
  /* MINGW doesn't do buffering right */
  setvbuf(stdout, NULL, _IOLBF, BUFSIZ);
  setvbuf(stderr, NULL, _IONBF, BUFSIZ);
#endif

#ifdef INITIALIZATION
  main_setup(); /* Do platform specific start-up. */
#endif

#ifdef CLOCK_INIT
  CLOCK_INIT();
#endif

#if WANT_SIGINT
  (void)signal(SIGINT, handle_sigint);
#endif

  heap_size = HEAP_CELLS;       /* number of heap cells */
  stack_size = STACK_SIZE;      /* number of stack slots */

#if WANT_ARGS
  progname = argv[0];
  argc--, argv++;
  gargv = argv;
  for (av = argv, inrts = 0; argc--; argv++) {
    char *p = *argv;
    if (inrts) {
      if (strcmp(p, "-RTS") == 0) {
        inrts = 0;
      } else {
        if (strcmp(p, "-v") == 0)
          verbose++;
#if WANT_TICK
        else if (strcmp(p, "-T") == 0)
          dump_ticks = 1;
#endif
        else if (strncmp(p, "-H", 2) == 0)
          heap_size = memsize(&p[2]);
        else if (strncmp(p, "-K", 2) == 0)
          stack_size = memsize(&p[2]);
        else if (strncmp(p, "-r", 2) == 0)
          inname = &p[2];
#if WANT_STDIO
        else if (strncmp(p, "-o", 2) == 0)
          outname = &p[2];
        else if (strcmp(p, "-B") == 0)
          gcbell++;
#endif  /* WANT_STDIO */
        else
          ERR("Usage: eval [+RTS [-v] [-B] [-T] [-Hheap-size] [-Kstack-size] [-rFILE] [-oFILE] -RTS] arg ...");
      }
    } else {
      if (strcmp(p, "+RTS") == 0) {
        inrts = 1;
      } else {
        *av++ = p;
      }
    }
  }
  gargc = av - gargv;

  if (inname == 0)
    inname = "out.comb";
#endif

  init_nodes();
  stack = mmalloc(sizeof(NODEPTR) * stack_size);
  CLEARSTK();
  num_reductions = 0;

#if WANT_ARGS
  /* Initialize an IORef (i.e., single element IOArray
   * to contain the list of program arguments.
   * The 0th element is the program name, and the rest
   * are the non RTS arguments.
   */
  {
    NODEPTR n;
    /* No GC checks, the heap is empty. */
    n = mkNil();
    for(int i = gargc-1; i >= 0; i--) {
      n = mkCons(mkStringC(gargv[i]), n);
    }
    n = mkCons(mkStringC(progname), n);
    argarray = arr_alloc(1, n);      /* An IORef contains a single element array */
    argarray->permanent = 1;         /* never GC the arguments, because a T_IO_GETARGREF can reach argarray */
  }
#endif  /* WANT_ARGS */

  if (combexpr) {
    int c;
    BFILE *bf = openb_rd_buf(combexpr, combexprlen);
    c = getb(bf);
    /* Compressed combinators start with a 'Z' or 'z', otherwise 'v' (for version) */
    if (c == 'z') {
      /* add LZ77 compressor transducer */
      bf = add_lz77_decompressor(bf);
    } else {
      /* put it back, we need it */
      ungetb(c, bf);
    }
    prog = parse_top(bf);
    closeb(bf);
#if WANT_STDIO
    file_size = combexprlen;
#endif
  } else {
#if WANT_STDIO
    prog = parse_file(inname, &file_size);
#else
    ERR("no stdio");
#endif
  }

  /* GC unused stuff, nice for -o */
  PUSH(prog);
  want_gc_red = 1;
  gc();
  gc();                         /* this finds some more GC reductions */
  want_gc_red = 0;              /* disabled due to UB */
  prog = POPTOP();

#if WANT_STDIO
  heapoffs_t start_size = num_marked;
  if (outname) {
    /* Save GCed file (smaller), and exit. */
    FILE *out = fopen(outname, "w");
    if (!out)
      ERR1("cannot open output file %s", outname);
    struct BFILE *bf = add_FILE(out);
    printb(bf, prog, 1);
    closeb(bf);
    EXIT(0);
  }
  if (verbose > 2) {
    pp(stdout, prog);
  }
#endif
  run_time -= GETTIMEMILLI();

  topnode = &prog;
  start_exec(prog);
  /* Flush standard handles in case there is some BFILE buffering */
  flushb((BFILE*)FORPTR(comb_stdout)->payload.string);
  flushb((BFILE*)FORPTR(comb_stderr)->payload.string);
  gc();                      /* Run finalizers */
  run_time += GETTIMEMILLI();

#if WANT_STDIO
  if (verbose) {
    if (verbose > 1) {
      PRINT("node size=%"PRIheap", heap size bytes=%"PRIheap"\n", (heapoffs_t)NODE_SIZE, heap_size * NODE_SIZE);
    }
    setlocale(LC_NUMERIC, "en_US");  /* Make %' work on platforms that support it */
    PRINT("%"PCOMMA"15"PRIheap" combinator file size\n", (heapoffs_t)file_size);
    PRINT("%"PCOMMA"15"PRIheap" cells at start\n", start_size);
    PRINT("%"PCOMMA"15"PRIheap" cells heap size (%"PCOMMA""PRIheap" bytes)\n", heap_size, heap_size * NODE_SIZE);
    PRINT("%"PCOMMA"15"PRIcounter" cells allocated (%"PCOMMA".1f Mbyte/s)\n", num_alloc, num_alloc * NODE_SIZE / ((double)run_time / 1000) / 1000000);
    PRINT("%"PCOMMA"15"PRIcounter" GCs\n", num_gc);
    PRINT("%"PCOMMA"15"PRIcounter" max cells used\n", max_num_marked);
    PRINT("%"PCOMMA"15"PRIcounter" reductions (%"PCOMMA".1f Mred/s)\n", num_reductions, num_reductions / ((double)run_time / 1000) / 1000000);
    PRINT("%"PCOMMA"15"PRIcounter" yields (%"PCOMMA""PRIcounter" resched)\n", num_yield, num_resched);
    PRINT("%"PCOMMA"15"PRIcounter" array alloc\n", num_arr_alloc);
    PRINT("%"PCOMMA"15"PRIcounter" array free\n", num_arr_free);
    PRINT("%"PCOMMA"15"PRIcounter" foreign alloc\n", num_fin_alloc);
    PRINT("%"PCOMMA"15"PRIcounter" foreign free\n", num_fin_free);
    PRINT("%"PCOMMA"15"PRIcounter" bytestring alloc (max %"PCOMMA""PRIcounter")\n", num_bs_alloc, num_bs_alloc_max);
    PRINT("%"PCOMMA"15"PRIcounter" bytestring alloc bytes (max %"PCOMMA""PRIcounter")\n", num_bs_bytes, num_bs_inuse_max);
    PRINT("%"PCOMMA"15"PRIcounter" bytestring free\n", num_bs_free);
    PRINT("%"PCOMMA"15"PRIcounter" thread create\n", num_thread_create-1);
    PRINT("%"PCOMMA"15"PRIcounter" thread reap\n", num_thread_reap);
#if MAXSTACKDEPTH
    PRINT("%"PCOMMA"15d max stack depth\n", (int)max_stack_depth);
    PRINT("%"PCOMMA"15d max C stack depth\n", (int)max_c_stack);
#endif
    // PRINT("%"PCOMMA"15"PRIcounter" max mark depth\n", max_mark_depth);
    PRINT("%15.2fs total expired time\n", (double)run_time / 1000);
    PRINT("%15.2fs total gc time (%.2f + %.2f)\n",
          (double)(gc_mark_time + gc_scan_time) / 1000,
          (double)gc_mark_time / 1000,
          (double)gc_scan_time / 1000);
#if GCRED
    PRINT(" GC reductions A=%"PRIcounter", K=%"PRIcounter", I=%"PRIcounter", int=%"PRIcounter", flip=%"PRIcounter","
          " BI=%"PRIcounter", BxI=%"PRIcounter", C'BxI=%"PRIcounter", CC=%"PRIcounter", C'I=%"PRIcounter", C'BBCP=%"PRIcounter"\n",
          red_a, red_k, red_i, red_int, red_flip, red_bi, red_bxi, red_ccbi, red_cc, red_cci, red_ccbbcp);
    PRINT(" special reductions B'=%"PRIcounter" K4=%"PRIcounter" K3=%"PRIcounter" K2=%"PRIcounter" C'B=%"PRIcounter", Z=%"PRIcounter", R=%"PRIcounter"\n",
          red_bb, red_k4, red_k3, red_k2, red_ccb, red_z, red_r);
#endif
  }
#endif  /* WANT_STDIO */

#if WANT_TICK
  if (dump_ticks) {
    dump_tick_table(stdout);
  }
#endif

#ifdef TEARDOWN
  main_teardown(); /* do some platform specific teardown */
#endif
  EXIT(0);
}

#if WANT_MD5
#include "md5.c"
#endif  /* WANT_MD5 */

#if WANT_LZ77
#include "lz77.c"
#endif

/*********************/
/* FFI adapters      */

#define MHS_FROM(name, set, type) \
from_t \
name(stackptr_t stk, int n, type x) \
{ \
  NODEPTR r = TOP(0);           /* The pre-allocated cell for the result, */ \
  set(r, x);                    /* Put result in pre-allocated cell. */ \
  return n;                     /* return arity */ \
}
MHS_FROM(mhs_from_FloatW, SETDBL, flt_t);
MHS_FROM(mhs_from_Int, SETINT, value_t);
MHS_FROM(mhs_from_Word, SETINT, uvalue_t);
MHS_FROM(mhs_from_Word8, SETINT, uvalue_t);
MHS_FROM(mhs_from_Ptr, SETPTR, void*);
MHS_FROM(mhs_from_ForPtr, SETFORPTR, struct forptr *);
MHS_FROM(mhs_from_FunPtr, SETFUNPTR, HsFunPtr);
MHS_FROM(mhs_from_CChar, SETINT, char);
MHS_FROM(mhs_from_CSChar, SETINT, signed char);
MHS_FROM(mhs_from_CUChar, SETINT, unsigned char);
MHS_FROM(mhs_from_CShort, SETINT, short);
MHS_FROM(mhs_from_CUShort, SETINT, unsigned short);
MHS_FROM(mhs_from_CInt, SETINT, int);
MHS_FROM(mhs_from_CUInt, SETINT, unsigned int);
MHS_FROM(mhs_from_CLong, SETINT, long);
MHS_FROM(mhs_from_CULong, SETINT, unsigned long);
MHS_FROM(mhs_from_CLLong, SETINT, long long);
MHS_FROM(mhs_from_CULLong, SETINT, unsigned long long);
MHS_FROM(mhs_from_CSize, SETINT, size_t);
#if WANT_TIME
MHS_FROM(mhs_from_CTime, SETINT, time_t);
#endif
// MHS_FROM(mhs_from_CSSize, SETINT, ssize_t);
MHS_FROM(mhs_from_CIntPtr, SETINT, intptr_t);
MHS_FROM(mhs_from_CUIntPtr, SETINT, uintptr_t);
from_t
mhs_from_Unit(stackptr_t stk, int n)
{
  POP(1);                       /* return value cell */
  PUSH(combUnit);               /* push unit instead */
  return n;
}

#define MHS_TO(name, eval, type) \
type name(stackptr_t stk, int n) \
{ \
  return eval(ARG(TOP(n+1)));                /* The stack has a reserved cell on top of the arguments */ \
}
MHS_TO(mhs_to_FloatW, evaldbl, flt_t);
MHS_TO(mhs_to_Int, evalint, value_t);
MHS_TO(mhs_to_Word, evalint, uvalue_t);
MHS_TO(mhs_to_Word8, evalint, uint8_t);
MHS_TO(mhs_to_Ptr, evalptr, void*);
MHS_TO(mhs_to_FunPtr, evalfunptr, HsFunPtr);
MHS_TO(mhs_to_CChar, evalint, char);
MHS_TO(mhs_to_CSChar, evalint, signed char);
MHS_TO(mhs_to_CUChar, evalint, unsigned char);
MHS_TO(mhs_to_CShort, evalint, short);
MHS_TO(mhs_to_CUShort, evalint, unsigned short);
MHS_TO(mhs_to_CInt, evalint, int);
MHS_TO(mhs_to_CUInt, evalint, unsigned int);
MHS_TO(mhs_to_CLong, evalint, long);
MHS_TO(mhs_to_CULong, evalint, unsigned long);
MHS_TO(mhs_to_CLLong, evalint, long long);
MHS_TO(mhs_to_CULLong, evalint, unsigned long long);
MHS_TO(mhs_to_CSize, evalint, size_t);
#if WANT_TIME
MHS_TO(mhs_to_CTime, evalint, time_t);
#endif
// MHS_TO(mhs_to_CSSize, evalint, ssize_t);
MHS_TO(mhs_to_CIntPtr, evalint, intptr_t);
MHS_TO(mhs_to_CUIntPtr, evalint, uintptr_t);


/* The rest of this file was generated by the compiler, with some minor edits with #if. */
from_t mhs_GETRAW(int s) { return  mhs_from_Int(s, 0, GETRAW()); }
from_t mhs_GETTIMEMILLI(int s) { return  mhs_from_Int(s, 0, GETTIMEMILLI()); }
#if WANT_MATH
#if WORD_SIZE == 64
from_t mhs_acos(int s) { return mhs_from_FloatW(s, 1, acos(mhs_to_FloatW(s, 0))); }
from_t mhs_asin(int s) { return mhs_from_FloatW(s, 1, asin(mhs_to_FloatW(s, 0))); }
from_t mhs_atan(int s) { return mhs_from_FloatW(s, 1, atan(mhs_to_FloatW(s, 0))); }
from_t mhs_atan2(int s) { return mhs_from_FloatW(s, 2, atan2(mhs_to_FloatW(s, 0), mhs_to_FloatW(s, 1))); }
from_t mhs_cos(int s) { return mhs_from_FloatW(s, 1, cos(mhs_to_FloatW(s, 0))); }
from_t mhs_exp(int s) { return mhs_from_FloatW(s, 1, exp(mhs_to_FloatW(s, 0))); }
from_t mhs_log(int s) { return mhs_from_FloatW(s, 1, log(mhs_to_FloatW(s, 0))); }
from_t mhs_sin(int s) { return mhs_from_FloatW(s, 1, sin(mhs_to_FloatW(s, 0))); }
from_t mhs_sqrt(int s) { return mhs_from_FloatW(s, 1, sqrt(mhs_to_FloatW(s, 0))); }
from_t mhs_tan(int s) { return mhs_from_FloatW(s, 1, tan(mhs_to_FloatW(s, 0))); }
#elif WORD_SIZE == 32  /* WORD_SIZE */
from_t mhs_acos(int s) { return mhs_from_FloatW(s, 1, acosf(mhs_to_FloatW(s, 0))); }
from_t mhs_asin(int s) { return mhs_from_FloatW(s, 1, asinf(mhs_to_FloatW(s, 0))); }
from_t mhs_atan(int s) { return mhs_from_FloatW(s, 1, atanf(mhs_to_FloatW(s, 0))); }
from_t mhs_atan2(int s) { return mhs_from_FloatW(s, 2, atan2f(mhs_to_FloatW(s, 0), mhs_to_FloatW(s, 1))); }
from_t mhs_cos(int s) { return mhs_from_FloatW(s, 1, cosf(mhs_to_FloatW(s, 0))); }
from_t mhs_exp(int s) { return mhs_from_FloatW(s, 1, expf(mhs_to_FloatW(s, 0))); }
from_t mhs_log(int s) { return mhs_from_FloatW(s, 1, logf(mhs_to_FloatW(s, 0))); }
from_t mhs_sin(int s) { return mhs_from_FloatW(s, 1, sinf(mhs_to_FloatW(s, 0))); }
from_t mhs_sqrt(int s) { return mhs_from_FloatW(s, 1, sqrtf(mhs_to_FloatW(s, 0))); }
from_t mhs_tan(int s) { return mhs_from_FloatW(s, 1, tanf(mhs_to_FloatW(s, 0))); }
#else
#error Unknown WORD_SIZE
#endif  /* WORD_SIZE */
#endif  /* WANT_MATH */

#if WANT_STDIO
from_t mhs_add_FILE(int s) { return mhs_from_Ptr(s, 1, add_FILE(mhs_to_Ptr(s, 0))); }
from_t mhs_add_utf8(int s) { return mhs_from_Ptr(s, 1, add_utf8(mhs_to_Ptr(s, 0))); }
from_t mhs_closeb(int s) { closeb(mhs_to_Ptr(s, 0)); return mhs_from_Unit(s, 1); }
from_t mhs_addr_closeb(int s) { return mhs_from_FunPtr(s, 0, (HsFunPtr)&closeb); }
from_t mhs_flushb(int s) { flushb(mhs_to_Ptr(s, 0)); return mhs_from_Unit(s, 1); }
from_t mhs_fopen(int s) { return mhs_from_Ptr(s, 2, fopen(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1))); }

from_t mhs_getb(int s) { return mhs_from_Int(s, 1, getb(mhs_to_Ptr(s, 0))); }
from_t mhs_putb(int s) { putb(mhs_to_Int(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_ungetb(int s) { ungetb(mhs_to_Int(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_openwrbuf(int s) { return mhs_from_Ptr(s, 0, openb_wr_buf()); }
from_t mhs_openrdbuf(int s) { return mhs_from_Ptr(s, 2, openb_rd_buf(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1))); }
from_t mhs_getbuf(int s) { get_buf(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2));  return mhs_from_Unit(s, 3); }
from_t mhs_system(int s) { return mhs_from_Int(s, 1, system(mhs_to_Ptr(s, 0))); }
from_t mhs_tmpname(int s) { return mhs_from_Ptr(s, 2, TMPNAME(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1))); }
from_t mhs_unlink(int s) { return mhs_from_Int(s, 1, unlink(mhs_to_Ptr(s, 0))); }
from_t mhs_readb(int s) { return mhs_from_Int(s, 3, readb(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1), mhs_to_Ptr(s, 2))); }
from_t mhs_writeb(int s) { return mhs_from_Int(s, 3, writeb(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1), mhs_to_Ptr(s, 2))); }
from_t mhs_putchar(int s) { putchar(mhs_to_Int(s, 0)); return mhs_from_Unit(s, 1); } /* for debugging */
#endif  /* WANT_STDIO */

#if WANT_MD5
from_t mhs_md5Array(int s) { md5Array(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Int(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_md5BFILE(int s) { md5BFILE(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_md5String(int s) { md5String(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WANT_MD5 */

#if WANT_LZ77
from_t mhs_add_lz77_compressor(int s) { return mhs_from_Ptr(s, 1, add_lz77_compressor(mhs_to_Ptr(s, 0))); }
from_t mhs_add_lz77_decompressor(int s) { return mhs_from_Ptr(s, 1, add_lz77_decompressor(mhs_to_Ptr(s, 0))); }
from_t mhs_lz77c(int s) { return mhs_from_CSize(s, 3, lz77c(mhs_to_Ptr(s, 0), mhs_to_CSize(s, 1), mhs_to_Ptr(s, 2))); }
#endif  /* WANT_LZ77 */

#if WANT_RLE
from_t mhs_add_rle_compressor(int s) { return mhs_from_Ptr(s, 1, add_rle_compressor(mhs_to_Ptr(s, 0))); }
from_t mhs_add_rle_decompressor(int s) { return mhs_from_Ptr(s, 1, add_rle_decompressor(mhs_to_Ptr(s, 0))); }
#endif  /* WANT_RLE */

#if WANT_BWT
from_t mhs_add_bwt_compressor(int s) { return mhs_from_Ptr(s, 1, add_bwt_compressor(mhs_to_Ptr(s, 0))); }
from_t mhs_add_bwt_decompressor(int s) { return mhs_from_Ptr(s, 1, add_bwt_decompressor(mhs_to_Ptr(s, 0))); }
#endif  /* WANT_BWT */

from_t mhs_calloc(int s) { return mhs_from_Ptr(s, 2, calloc(mhs_to_CSize(s, 0), mhs_to_CSize(s, 1))); }
from_t mhs_free(int s) { free(mhs_to_Ptr(s, 0)); return mhs_from_Unit(s, 1); }
from_t mhs_addr_free(int s) { return mhs_from_FunPtr(s, 0, (HsFunPtr)&FREE); }
from_t mhs_getenv(int s) { return mhs_from_Ptr(s, 1, getenv(mhs_to_Ptr(s, 0))); }
from_t mhs_iswindows(int s) { return mhs_from_Int(s, 0, iswindows()); }
from_t mhs_malloc(int s) { return mhs_from_Ptr(s, 1, MALLOC(mhs_to_CSize(s, 0))); }
from_t mhs_memcpy(int s) { memcpy(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_CSize(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_memmove(int s) { memmove(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_CSize(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_peekPtr(int s) { return mhs_from_Ptr(s, 1, peekPtr(mhs_to_Ptr(s, 0))); }
from_t mhs_peekWord(int s) { return mhs_from_Word(s, 1, peekWord(mhs_to_Ptr(s, 0))); }
from_t mhs_pokePtr(int s) { pokePtr(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_pokeWord(int s) { pokeWord(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }

from_t mhs_peek_uint8(int s) { return mhs_from_Word(s, 1, peek_uint8(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_uint8(int s) { poke_uint8(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_peek_uint16(int s) { return mhs_from_Word(s, 1, peek_uint16(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_uint16(int s) { poke_uint16(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }
#if WORD_SIZE >= 32
from_t mhs_peek_uint32(int s) { return mhs_from_Word(s, 1, peek_uint32(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_uint32(int s) { poke_uint32(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WORD_SIZE */
#if WORD_SIZE >= 64
from_t mhs_peek_uint64(int s) { return mhs_from_Word(s, 1, peek_uint64(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_uint64(int s) { poke_uint64(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WORD_SIZE */
from_t mhs_peek_uint(int s) { return mhs_from_Word(s, 1, peek_uint(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_uint(int s) { poke_uint(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }

from_t mhs_peek_int8(int s) { return mhs_from_Int(s, 1, peek_int8(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_int8(int s) { poke_int8(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_peek_int16(int s) { return mhs_from_Int(s, 1, peek_int16(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_int16(int s) { poke_int16(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
#if WORD_SIZE >= 32
from_t mhs_peek_int32(int s) { return mhs_from_Int(s, 1, peek_int32(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_int32(int s) { poke_int32(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WORD_SIZE */
#if WORD_SIZE >= 64
from_t mhs_peek_int64(int s) { return mhs_from_Int(s, 1, peek_int64(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_int64(int s) { poke_int64(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WORD_SIZE */
from_t mhs_peek_int(int s) { return mhs_from_Int(s, 1, peek_int(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_int(int s) { poke_int(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_peek_llong(int s) { return mhs_from_CLLong(s, 1, peek_llong(mhs_to_Ptr(s, 0))); }
from_t mhs_peek_long(int s) { return mhs_from_CLong(s, 1, peek_long(mhs_to_Ptr(s, 0))); }
from_t mhs_peek_ullong(int s) { return mhs_from_CULLong(s, 1, peek_ullong(mhs_to_Ptr(s, 0))); }
from_t mhs_peek_ulong(int s) { return mhs_from_CULong(s, 1, peek_ulong(mhs_to_Ptr(s, 0))); }
from_t mhs_peek_size_t(int s) { return mhs_from_CSize(s, 1, peek_size_t(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_llong(int s) { poke_llong(mhs_to_Ptr(s, 0), mhs_to_CLLong(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_poke_long(int s) { poke_long(mhs_to_Ptr(s, 0), mhs_to_CLong(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_poke_ullong(int s) { poke_ullong(mhs_to_Ptr(s, 0), mhs_to_CULLong(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_poke_ulong(int s) { poke_ulong(mhs_to_Ptr(s, 0), mhs_to_CULong(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_poke_size_t(int s) { poke_size_t(mhs_to_Ptr(s, 0), mhs_to_CSize(s, 1)); return mhs_from_Unit(s, 2); }
#if WANT_FLOAT
from_t mhs_peek_flt(int s) { return mhs_from_FloatW(s, 1, peek_flt(mhs_to_Ptr(s, 0))); }
from_t mhs_poke_flt(int s) { poke_flt(mhs_to_Ptr(s, 0), mhs_to_FloatW(s, 1)); return mhs_from_Unit(s, 2); }
#endif  /* WANT_FLOAT */
from_t mhs_sizeof_int(int s) { return mhs_from_Int(s, 0, sizeof(int)); }
from_t mhs_sizeof_llong(int s) { return mhs_from_Int(s, 0, sizeof(long long)); }
from_t mhs_sizeof_long(int s) { return mhs_from_Int(s, 0, sizeof(long)); }
from_t mhs_sizeof_size_t(int s) { return mhs_from_Int(s, 0, sizeof(size_t)); }
#if WANT_DIR
from_t mhs_closedir(int s) { return mhs_from_Int(s, 1, closedir(mhs_to_Ptr(s, 0))); }
from_t mhs_opendir(int s) { return mhs_from_Ptr(s, 1, opendir(mhs_to_Ptr(s, 0))); }
from_t mhs_readdir(int s) { return mhs_from_Ptr(s, 1, readdir(mhs_to_Ptr(s, 0))); }
from_t mhs_c_d_name(int s) { return mhs_from_Ptr(s, 1, ((struct dirent *)(mhs_to_Ptr(s, 0)))->d_name); }
from_t mhs_chdir(int s) { return mhs_from_Int(s, 1, chdir(mhs_to_Ptr(s, 0))); }
from_t mhs_mkdir(int s) { return mhs_from_Int(s, 2, mkdir(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1))); }
from_t mhs_getcwd(int s) { return mhs_from_Ptr(s, 2, getcwd(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1))); }
#endif  /* WANT_DIR */
from_t mhs_getcpu(int s) { GETCPUTIME(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }

/* Use this to detect if we have (and want) GMP or not. */
from_t mhs_want_gmp(int s) { return mhs_from_Int(s, 0, WANT_GMP); }

#if WANT_GMP
void
free_mpz(void *p)
{
  /*  printf("free_mpz %p\n", p);*/
  mpz_clear(p);                 /* free any extra storage */
  FREE(p);                      /* and free the mpz itself */
}

/* Allocate an initialize a GMP integer */
struct forptr *
new_mpz(void)
{
#if 0
  {
    static int done = 0;
    if (!done) {
      printf("GMP\n");
      done = 1;
    }
  }
#endif
  mpz_ptr p = mmalloc(sizeof(*p));
  mpz_init(p);
  struct forptr *fp = mkForPtrP(p);
  fp->finalizer->final = (HsFunPtr)free_mpz;
  fp->finalizer->fptype = FP_MPZ;
  /*  printf("new_mpz %p %p\n", p, fp); */
  return fp;
}

#if 0
void
print_mpz(mpz_ptr p)
{
  mpz_out_str(stdout, 10, p);
}
#endif

from_t mhs_new_mpz(int s) { return mhs_from_ForPtr(s, 0, new_mpz()); }

/* Stubs for GMP functions */
from_t mhs_mpz_abs(int s) { mpz_abs(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_mpz_add(int s) { mpz_add(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_and(int s) { mpz_and(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_cmp(int s) { return mhs_from_Int(s, 2, mpz_cmp(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1))); }
from_t mhs_mpz_get_d(int s) { return mhs_from_FloatW(s, 1, mpz_get_d(mhs_to_Ptr(s, 0))); }
from_t mhs_mpz_get_si(int s) { return mhs_from_Int(s, 1, mpz_get_si(mhs_to_Ptr(s, 0))); }
from_t mhs_mpz_get_ui(int s) { return mhs_from_Word(s, 1, mpz_get_ui(mhs_to_Ptr(s, 0))); }
from_t mhs_mpz_init_set_si(int s) { mpz_init_set_si(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_mpz_init_set_ui(int s) { mpz_init_set_ui(mhs_to_Ptr(s, 0), mhs_to_Word(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_mpz_ior(int s) { mpz_ior(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_mul(int s) { mpz_mul(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_mul_2exp(int s) { mpz_mul_2exp(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Int(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_neg(int s) { mpz_neg(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1)); return mhs_from_Unit(s, 2); }
from_t mhs_mpz_popcount(int s) {
  mpz_ptr a = mhs_to_Ptr(s, 0);
  if (mpz_sgn(a) < 0) {
    mpz_t neg_a;
    mpz_init(neg_a);
    mpz_neg(neg_a, a);
    (void)mhs_from_Int(s, 1, -mpz_popcount(neg_a));
    mpz_clear(neg_a);
  } else {
    (void)mhs_from_Int(s, 1, mpz_popcount(a));
  }
  return 1;
}
from_t mhs_mpz_sub(int s) { mpz_sub(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_fdiv_q_2exp(int s) { mpz_fdiv_q_2exp(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Int(s, 2)); return mhs_from_Unit(s, 3); }
from_t mhs_mpz_tdiv_qr(int s) { mpz_tdiv_qr(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2), mhs_to_Ptr(s, 3)); return mhs_from_Unit(s, 4); }
from_t mhs_mpz_tstbit(int s) { return mhs_from_Int(s, 2, mpz_tstbit(mhs_to_Ptr(s, 0), mhs_to_Int(s, 1))); }
from_t mhs_mpz_xor(int s) { mpz_xor(mhs_to_Ptr(s, 0), mhs_to_Ptr(s, 1), mhs_to_Ptr(s, 2)); return mhs_from_Unit(s, 3); }
#endif  /* WANT_GMP */

struct ffi_entry ffi_table[] = {
  { "GETRAW", 0, mhs_GETRAW},
  { "GETTIMEMILLI", 0, mhs_GETTIMEMILLI},
#if WANT_MATH
  { "acos", 1, mhs_acos},
  { "asin", 1, mhs_asin},
  { "atan", 1, mhs_atan},
  { "atan2", 2, mhs_atan2},
  { "cos", 1, mhs_cos},
  { "exp", 1, mhs_exp},
  { "log", 1, mhs_log},
  { "sin", 1, mhs_sin},
  { "sqrt", 1, mhs_sqrt},
  { "tan", 1, mhs_tan},
#endif  /* WANT_MATH */

#if WANT_STDIO
  { "add_FILE", 1, mhs_add_FILE},
  { "add_utf8", 1, mhs_add_utf8},
  { "closeb", 1, mhs_closeb},
  { "&closeb", 0, mhs_addr_closeb},
  { "flushb", 1, mhs_flushb},
  { "fopen", 2, mhs_fopen},
  { "getb", 1, mhs_getb},
  { "putb", 2, mhs_putb},
  { "ungetb", 2, mhs_ungetb},
  { "openb_wr_buf", 0, mhs_openwrbuf},
  { "openb_rd_buf", 2, mhs_openrdbuf},
  { "get_buf", 3, mhs_getbuf},
  { "system", 1, mhs_system},
  { "tmpname", 2, mhs_tmpname},
  { "unlink", 1, mhs_unlink},
  { "readb", 3, mhs_readb},
  { "writeb", 3, mhs_writeb},
  { "putchar", 1, mhs_putchar},
#endif  /* WANT_STDIO */

#if WANT_MD5
  { "md5Array", 3, mhs_md5Array},
  { "md5BFILE", 2, mhs_md5BFILE},
  { "md5String", 2, mhs_md5String},
#endif  /* WANT_MD5 */

#if WANT_LZ77
  { "add_lz77_compressor", 1, mhs_add_lz77_compressor},
  { "add_lz77_decompressor", 1, mhs_add_lz77_decompressor},
  { "lz77c", 3, mhs_lz77c},
#endif  /* WANT_LZ77 */

#if WANT_RLE
  { "add_rle_compressor", 1, mhs_add_rle_compressor},
  { "add_rle_decompressor", 1, mhs_add_rle_decompressor},
#endif  /* WANT_RLE */

#if WANT_BWT
  { "add_bwt_compressor", 1, mhs_add_bwt_compressor},
  { "add_bwt_decompressor", 1, mhs_add_bwt_decompressor},
#endif  /* WANT_RLE */

  { "calloc", 2, mhs_calloc},
  { "free", 1, mhs_free},
  { "&free", 0, mhs_addr_free},
  { "getenv", 1, mhs_getenv},
  { "iswindows", 0, mhs_iswindows},
  { "malloc", 1, mhs_malloc},
  { "memcpy", 3, mhs_memcpy},
  { "memmove", 3, mhs_memmove},
  { "peekPtr", 1, mhs_peekPtr},
  { "peekWord", 1, mhs_peekWord},
  { "pokePtr", 2, mhs_pokePtr},
  { "pokeWord", 2, mhs_pokeWord},

  { "peek_uint8", 1, mhs_peek_uint8},
  { "poke_uint8", 2, mhs_poke_uint8},
  { "peek_uint16", 1, mhs_peek_uint16},
  { "poke_uint16", 2, mhs_poke_uint16},
#if WORD_SIZE >= 32
  { "peek_uint32", 1, mhs_peek_uint32},
  { "poke_uint32", 2, mhs_poke_uint32},
#endif  /* WORD_SIZE >= 32 */
#if WORD_SIZE >= 64
  { "peek_uint64", 1, mhs_peek_uint64},
  { "poke_uint64", 2, mhs_poke_uint64},
#endif  /* WORD_SIZE >= 64 */
  { "peek_uint", 1, mhs_peek_uint},
  { "poke_uint", 2, mhs_poke_uint},

  { "peek_int8", 1, mhs_peek_int8},
  { "poke_int8", 2, mhs_poke_int8},
  { "peek_int16", 1, mhs_peek_int16},
  { "poke_int16", 2, mhs_poke_int16},
#if WORD_SIZE >= 32
  { "peek_int32", 1, mhs_peek_int32},
  { "poke_int32", 2, mhs_poke_int32},
#endif  /* WORD_SIZE >= 32 */
#if WORD_SIZE >= 64
  { "peek_int64", 1, mhs_peek_int64},
  { "poke_int64", 2, mhs_poke_int64},
#endif  /* WORD_SIZE >= 64 */
  { "peek_int", 1, mhs_peek_int},
  { "poke_int", 2, mhs_poke_int},
  { "peek_llong", 1, mhs_peek_llong},
  { "peek_long", 1, mhs_peek_long},
  { "peek_ullong", 1, mhs_peek_ullong},
  { "peek_ulong", 1, mhs_peek_ulong},
  { "peek_size_t", 1, mhs_peek_size_t},
  { "poke_llong", 2, mhs_poke_llong},
  { "poke_long", 2, mhs_poke_long},
  { "poke_ullong", 2, mhs_poke_ullong},
  { "poke_ulong", 2, mhs_poke_ulong},
  { "poke_size_t", 2, mhs_poke_size_t},
#if WANT_FLOAT
  { "peek_flt", 1, mhs_peek_flt},
  { "poke_flt", 2, mhs_poke_flt},
#endif  /* WANT_FLOAT */
  { "sizeof_int", 0, mhs_sizeof_int},
  { "sizeof_llong", 0, mhs_sizeof_llong},
  { "sizeof_long", 0, mhs_sizeof_long},
  { "sizeof_size_t", 0, mhs_sizeof_size_t},
#if WANT_DIR
  { "c_d_name", 1, mhs_c_d_name},
  { "closedir", 1, mhs_closedir},
  { "opendir", 1, mhs_opendir},
  { "readdir", 1, mhs_readdir},
  { "chdir", 1, mhs_chdir},
  { "mkdir", 2, mhs_mkdir},
  { "getcwd", 2, mhs_getcwd},
#endif  /* WANT_DIR */
  { "getcpu", 2, mhs_getcpu},
  { "want_gmp", 0, mhs_want_gmp},
#if WANT_GMP
  { "new_mpz", 0, mhs_new_mpz},
  { "mpz_abs", 2, mhs_mpz_abs},
  { "mpz_add", 3, mhs_mpz_add},
  { "mpz_and", 3, mhs_mpz_and},
  { "mpz_cmp", 2, mhs_mpz_cmp},
  { "mpz_get_d", 1, mhs_mpz_get_d},
  { "mpz_get_si", 1, mhs_mpz_get_si},
  { "mpz_get_ui", 1, mhs_mpz_get_ui},
  { "mpz_init_set_si", 2, mhs_mpz_init_set_si},
  { "mpz_init_set_ui", 2, mhs_mpz_init_set_ui},
  { "mpz_ior", 3, mhs_mpz_ior},
  { "mpz_mul", 3, mhs_mpz_mul},
  { "mpz_mul_2exp", 3, mhs_mpz_mul_2exp},
  { "mpz_neg", 2, mhs_mpz_neg},
  { "mpz_popcount", 1, mhs_mpz_popcount},
  { "mpz_sub", 3, mhs_mpz_sub},
  { "mpz_fdiv_q_2exp", 3, mhs_mpz_fdiv_q_2exp},
  { "mpz_tdiv_qr", 4, mhs_mpz_tdiv_qr},
  { "mpz_tstbit", 2, mhs_mpz_tstbit},
  { "mpz_xor", 3, mhs_mpz_xor},
#endif  /* WANT_GMP */
  { 0,0 }
};

int num_ffi = sizeof(ffi_table) / sizeof(ffi_table[0]);
