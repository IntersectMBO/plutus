/* Copyright 2023 Lennart Augustsson
 * See LICENSE file for full license.
 */

/*
 * Various platform specific configuration.
 */
/*
 * Include stdio functions.
 * Without this none of the file I/O in System.IO is available.
 */
#define WANT_STDIO 1

/*
 * Include ops for floating point arithmetic.
 * Without this +,-,* etc will not be available for the Double type.
 */
#define WANT_FLOAT 1

/*
 * Include <math.h>
 * Without this exp,sin,sqrt etc will not be available.
 */
#define WANT_MATH 1

/*
 * Include MD5 checksumming code
 */
#define WANT_MD5 1

/*
 * Include profiling code
 */
#define WANT_TICK 1

/*
 * Include directory manipulation
 */
#define WANT_DIR 1

/*
 * Include time_t type
 */
#define WANT_TIME 1

/*
 * Number of bits in a word.  Only 32 and 64 are supported.
 * WORD_SIZE set in mhsffi.h
 */
//#define WORD_SIZE 64

/*
 * Find First Set
 * This macro should be defined.
 * It returns the number of the least significant bit that is set.
 * Numberings starts from 1.  If no bit is set, it should return 0.
 */
#if defined(__gnu_linux__) || defined(__APPLE__) || defined(__FreeBSD__)
/* Only some platforms have 64 bit ffsl function directly. */
#define FFS ffsl
#elif defined(__has_builtin)

#if __has_builtin(__builtin__ffsl)
#define FFS __builtin_ffsl
#endif

#endif

/*
 * This is the character used for comma-separation in printf.
 * Defaults to "'".
 */
/* #define PCOMMA "'" */

#include <inttypes.h>
#include <termios.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <fcntl.h>
#include <errno.h>
#if WANT_STDIO
#include <stdio.h>
#endif  /* WANT_STDIO */

/*
 * Set the terminal in raw mode and read a single character.
 * Return this character, or -1 on any kind of failure.
 */
static int
getraw(void)
{
  struct termios old, new;
  char c;
  int r;

#if defined(USE_SYSTEM_RAW)

  /* For, e.g., execution with WASM in node the ioctl() doesn't seem to work */
  system("stty raw");
  r = read(0, &c, 1);
  system("stty -raw");

#else  /* USE_SYSTEM_RAW */

  if (tcgetattr(0, &old)) {
#if WANT_STDIO
    fprintf(stderr, "tcgetattr failed: errno=%d\n", errno);
#endif  /* WANT_STDIO */
    return -1;
  }
  new = old;
  new.c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP
                   | INLCR | IGNCR | ICRNL | IXON);
  new.c_oflag &= ~OPOST;
  new.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
  new.c_cflag &= ~(CSIZE | PARENB);
  new.c_cflag |= CS8;
  if (tcsetattr(0, TCSANOW, &new)) {
#if WANT_STDIO
    fprintf(stderr, "tcsetattr 1 failed: errno=%d\n", errno);
#endif  /* WANT_STDIO */
    return -1;
  }
  r = read(0, &c, 1);
  if (tcsetattr(0, TCSANOW, &old)) {
#if WANT_STDIO
    fprintf(stderr, "tcsetattr 2 failed: errno=%d\n", errno);
#endif  /* WANT_STDIO */
    return -1;
  }

#endif  /* USE_SYSTEM_RAW */

  if (r == 1)
    return c;
  else {
#if WANT_STDIO
    fprintf(stderr, "read failed: errno=%d\n", errno);
#endif  /* WANT_STDIO */
    return -1;
  }
}
/*
 * Get a raw input character.
 * If undefined, the default always returns -1
 */
#define GETRAW getraw

/*
 * Get time since some epoch in milliseconds.
 */
#include <sys/time.h>
uintptr_t
gettimemilli(void)
{
  struct timeval tv;
  (void)gettimeofday(&tv, NULL);
  return (uintptr_t)(tv.tv_sec * 1000 + tv.tv_usec / 1000);
}
#define GETTIMEMILLI gettimemilli

/*
 * Create a unique file name.
 * This is a very dodgy implementation.
 * XXX This functions drags in a lot of functionality.
 */
char*
tmpname(const char* pre, const char* suf)
{
  int pid = (int)getpid();
  char *tmp = getenv("TMPDIR");
  const size_t PID_DIGITS = 10;
  if (!tmp)
    tmp = "/tmp";
  char *s = malloc(strlen(tmp) + 1 + strlen(pre) + PID_DIGITS + strlen(suf) + 1);
  /* This might loop forever.  See if I care. :) */
  for(;;) {
    strcpy(s, tmp);
    strcat(s, "/");
    strcat(s, pre);
    /* Insert PID_DIGITS digits of the PID */
    char *p = s + strlen(s) + PID_DIGITS;
    *p-- = 0;
    for(int i = 0; i < PID_DIGITS; i++) {
      *p-- = pid % 10 + '0';
      pid /= 10;
    }
    strcat(s, suf);
    /* The file name is ready, do a quick if check that we can create it */
    int fd = open(s, O_CREAT | O_EXCL, 0600);
    if (fd >= 0) {
      close(fd);                /* Close it again */
      return s;
    }
    pid++;                      /* try with a different pid */
  }
}
#define TMPNAME tmpname

/*
 * Define CLOCK_INIT is there is a ticking clock.
 * CLOCK_INIT will be called for initializing the clock
 */
/* On Unix we just use gettimeofday() to get the clock,
 * so no initialization is needed.
 */
#define CLOCK_INIT() do { } while(0)
/* CLOCK_T is the type of the clock values. */
#define CLOCK_T int64_t       /* large enough for 290Myears */
/* CLOCK_GET returns the current clock in microseconds. */
#define CLOCK_GET clock_get
/* CLOCK_SLEEP sleeps some number of microseconds */
#define CLOCK_SLEEP usleep
CLOCK_T CLOCK_GET(void)
{
  struct timeval tv;
  (void)gettimeofday(&tv, 0);   /* this is very fast, about 16ns on an M4 MacMini */
  return (uint64_t)(tv.tv_sec * 1000000 + tv.tv_usec);
}

#include <time.h>
void
getcputime(long *sec, long *nsec)
{
#if WANT_TIME
  struct timespec ts;
  
  if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts) == 0) {
    *sec = ts.tv_sec;
    *nsec = ts.tv_nsec;
    return;
  }
#endif
  *sec = 0;
  *nsec = 0;
}
#define GETCPUTIME getcputime

/*
 * We want a signal handler for SIGINT.
 */
#define WANT_SIGINT 1

/*
 * The ERR macro should report an error and exit.
 * If not defined, a generic one will be used.
 */
/* #define ERR(s) */
/* #define ERR1(s,a) */

#define GCRED    1              /* do some reductions during GC */
#define INTTABLE 1              /* use fixed table of small INT nodes */
#define SANITY   1              /* do some sanity checks */
#define STACKOVL 1              /* check for stack overflow */
