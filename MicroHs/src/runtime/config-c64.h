/*
 * Various platform specific configuration.
 */

/*
 * Include stdio functions.
 * Without this none of the file I/O in System.IO is available.
 */
#define WANT_STDIO 0

/*
 * Include ops for floating point arithmetic.
 * Without this +,-,* etc will not be available for the Double type.
 */
#define WANT_FLOAT 0

/*
 * Include <math.h>
 * Without this, exp,sin, etc are not available.
 */
#define WANT_MATH 0

/*
 * Include MD5 checksumming code
 */
#define WANT_MD5 0

/*
 * Include profiling code
 */
#define WANT_TICK 0

/*
 * Process argc, argv
 */
#define WANT_ARGS 0

/*
 * Number of bits in a word.  Only 32 and 64 are supported.
 */
//#define WORD_SIZE 16

/*
 * Find First Set
 * This macro must be defined.
 * It return the number of the least significant bit that is set.
 * Numberings starts from 1.  If no bit is set, it should return 0.
 */
/* #define FFS ffsl */

/*
 * This is the character used for comma-separation in printf.
 * Defaults to "'".
 */
/* #define PCOMMA "'" */


/*
 * Get a raw input character.
 * If undefined, the default always returns -1
 */
/* #define GETRAW */


/*
 * Get time since some epoch in milliseconds.
 */
/* #define GETTIMEMILLI */


/*
 * The ERR macro should report an error and exit.
 * If not defined, a generic one will be used.
 */
/* #define ERR(s) */
/* #define ERR1(s,a) */

#define GCRED    0              /* do some reductions during GC */
#define INTTABLE 0              /* use fixed table of small INT nodes */
#define SANITY   0              /* do some sanity checks */
#define STACKOVL 1              /* check for stack overflow */

#define INLINE
#define NORETURN
