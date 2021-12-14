-- |
-- Module      :  Foundation.System.Bindings.HostName
-- License     :  BSD-style
-- Maintainer  :  Nicolas Di Prima <nicolas@primetype.co.uk>
-- Stability   :  provisional
-- Portability :  portable
--
{-# OPTIONS_HADDOCK hide #-}
module Foundation.System.Bindings.Network
    ( -- * error
      getHErrno
    , herr_HostNotFound
    , herr_NoData
    , herr_NoRecovery
    , herr_TryAgain
    ) where

import Basement.Compat.Base
import Basement.Compat.C.Types

#ifdef mingw32_HOST_OS
# include <winsock2.h>
#else
# include "netinet/in.h"
# include "netdb.h"
#endif

herr_HostNotFound
  , herr_NoData
  , herr_NoRecovery
  , herr_TryAgain
    :: CInt
#ifdef mingw32_HOST_OS
herr_HostNotFound = (#const WSAHOST_NOT_FOUND)
herr_NoData       = (#const WSANO_DATA)
herr_NoRecovery   = (#const WSANO_RECOVERY)
herr_TryAgain     = (#const WSATRY_AGAIN)
#else
herr_HostNotFound = (#const HOST_NOT_FOUND)
herr_NoData       = (#const NO_DATA)
herr_NoRecovery   = (#const NO_RECOVERY)
herr_TryAgain     = (#const TRY_AGAIN)
#endif

foreign import ccall unsafe "foundation_network_get_h_errno"
    getHErrno :: IO CInt
