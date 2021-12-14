#include "foundation_system.h"

#if defined(FOUNDATION_SYSTEM_WINDOWS)
# include <winsock2.h>
#else
# include "netdb.h"
#endif


int foundation_network_get_h_errno(void)
{
#if defined(FOUNDATION_SYSTEM_WINDOWS)
  return WSAGetLastError();
#else
  return h_errno;
#endif
}
