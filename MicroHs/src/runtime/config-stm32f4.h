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
#define WANT_FLOAT 1

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
//#define WORD_SIZE 32

/*
 * Find First Set
 * This macro must be defined.
 * It return the number of the least significant bit that is set.
 * Numberings starts from 1.  If no bit is set, it should return 0.
 */
// #define FFS

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
#define INTTABLE 1              /* use fixed table of small INT nodes */
#define SANITY   1              /* do some sanity checks */
#define STACKOVL 1              /* check for stack overflow */

#define HEAP_CELLS 4000
#define STACK_SIZE 500

#include "stm32f4xx.h"

#define INITIALIZATION
void
main_setup(void)
{
  RCC->AHB1ENR |= RCC_AHB1ENR_GPIODEN; // Enable the clock of port D of the GPIO
	
  GPIOD->MODER |= GPIO_MODER_MODER12_0; // Green LED, set pin 12 as output
  GPIOD->MODER |= GPIO_MODER_MODER13_0; // Orange LED, set pin 13 as output
  GPIOD->MODER |= GPIO_MODER_MODER14_0; // Red LED, set pin 14 as output
  GPIOD->MODER |= GPIO_MODER_MODER15_0; // Blue LED, set pin 15 as output
}

void
set_led(int led, int on)
{
  GPIOD->BSRR = 1 << (12 + led + (on ? 0 : 16));
}

#pragma push
#pragma O0
void
busy_wait(volatile uint32_t cnt) {
  while(cnt--)
    _nop_();
}
#pragma pop

/* Instead of exit()ing, flash the green LED on exit code 0 else the red */
void
myexit(int n)
{
  set_led(0, 0);
  set_led(1, 0);
  set_led(2, 0);
  set_led(3, 0);
  int led = n ? 2 : 0;
  for(;;) {
    set_led(led, 1);
    busy_wait(1000000);
    set_led(led, 0);
    busy_wait(1000000);
  }
}
#define EXIT myexit

int
ffs(uintptr_t x)
{
  if (!x)
    return 0;
  x &= -x;                      /* keep lowest bit */
  int i = __CLZ(x);             /* count leading 0s */
  return 32 - i;                /* 31 leading zeros should return 1 */
}
#define FFS ffs

#define CLZ __CLZ

#define FFI_EXTRA \
  { "set_led",   (funptr_t)set_led,   FFI_IIV }, \
  { "busy_wait", (funptr_t)busy_wait, FFI_IV },
