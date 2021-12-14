{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnliftedFFITypes #-}
module Foundation.System.Bindings.Hs
    where

import GHC.IO
import Basement.Compat.C.Types

foreign import ccall unsafe "HsBase.h __hscore_get_errno" sysHsCoreGetErrno :: IO CInt
