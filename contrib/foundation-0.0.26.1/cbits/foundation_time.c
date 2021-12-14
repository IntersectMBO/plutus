#include "foundation_system.h"

#ifdef FOUNDATION_SYSTEM_API_NO_CLOCK

typedef enum {
	FOUNDATION_CLOCK_REALTIME,
	FOUNDATION_CLOCK_MONOTONIC,
	FOUNDATION_CLOCK_PROCESS_CPUTIME_ID,
	FOUNDATION_CLOCK_THREAD_CPUTIME_ID
} foundation_clockid_t;


#ifdef FOUNDATION_SYSTEM_MACOS
#include <time.h>
#include <mach/clock.h>
#include <mach/mach.h>
#include <mach/mach_time.h>

/* OSX MONOTONIC COMPAT:
 * http://web.archive.org/web/20100517095152/http://www.wand.net.nz/~smr26/wordpress/2009/01/19/monotonic-time-in-mac-os-x/comment-page-1/
 */


static mach_timebase_info_data_t timebase = {0,0};

int foundation_time_clock_getres(unsigned int clockid, struct timespec *timespec)
{
	switch (clockid) {
	/* clockid = 1 (FOUNDATION_CLOCK_MONOTONIC), or any other value */
	case FOUNDATION_CLOCK_MONOTONIC:
		if (timebase.denom == 0) mach_timebase_info(&timebase);
		timespec->tv_sec = 0;
		timespec->tv_nsec = timebase.numer / timebase.denom;
		break;
	/* clockid = 0 (FOUNDATION_CLOCK_REALTIME), or any other value */
	case FOUNDATION_CLOCK_REALTIME:
		return -1;
	}
	return -1;
}

int foundation_time_clock_gettime(unsigned int clockid, struct timespec *timespec)
{
	clock_serv_t cclock;
	mach_timespec_t mts;

	switch (clockid) {
#if 0
	case CLOCK_MONOTONIC: {
		uint64_t t, nanos;
		if (timebase.denom == 0) mach_timebase_info(timebase);

		t = mach_absolute_time();
		nanos = t * (timebase.numer / timebase.denom);

		timespec->tv_sec = t / 1e9;
		timespec->tv_nsec = t % 1e9;
		break;
	case CLOCK_PROCESS_CPUTIME_ID:
		break;
#endif
	case FOUNDATION_CLOCK_MONOTONIC:
		host_get_clock_service(mach_host_self(), SYSTEM_CLOCK, &cclock);
		clock_get_time(cclock, &mts);
		mach_port_deallocate(mach_task_self(), cclock);
		timespec->tv_sec = mts.tv_sec;
		timespec->tv_nsec = mts.tv_nsec;
		break;
	case FOUNDATION_CLOCK_REALTIME:
		host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
		clock_get_time(cclock, &mts);
		mach_port_deallocate(mach_task_self(), cclock);
		timespec->tv_sec = mts.tv_sec;
		timespec->tv_nsec = mts.tv_nsec;
		break;
	default:
		return -1;
	}
	return 0;
}

#elif defined(FOUNDATION_SYSTEM_WINDOWS)

#include <windows.h>

// from:
// https://stackoverflow.com/questions/5404277/porting-clock-gettime-to-windows

struct timespec { long tv_sec; long tv_nsec; }; //header part

#define BILLION                             (1E9)

int foundation_time_clock_getres(unsigned int clockid, struct timespec *timespec)
{
}

int foundation_time_clock_gettime(unsigned int clockid, struct timespec *ct)
{
	LARGE_INTEGER count;
	static LARGE_INTEGER counts_per_sec = { .QuadPart = -1 };

	switch (clockid) {
	case FOUNDATION_CLOCK_MONOTONIC:
		if (counts_per_sec.QuadPart == -1) {
			if (0 == QueryPerformanceFrequency(&counts_per_sec)) {
				counts_per_sec.QuadPart = 0;
			}
		}

		if ((NULL == ct) || (counts_per_sec.QuadPart <= 0) || (0 == QueryPerformanceCounter(&count))) {
			return -1;
		}

		ct->tv_sec = count.QuadPart / counts_per_sec.QuadPart;
		ct->tv_nsec = ((count.QuadPart % counts_per_sec.QuadPart) * BILLION) / counts_per_sec.QuadPart;
		break;
	default:
		return -1;
	}
	return 0;
}

#endif

#endif
