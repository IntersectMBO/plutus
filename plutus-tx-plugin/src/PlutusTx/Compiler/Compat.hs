{-# LANGUAGE CPP #-}

module PlutusTx.Compiler.Compat
  ( maybeGetClassOpId
  ) where

import GHC.Core.Class qualified as GHC
import GHC.Types.Id.Info qualified as GHC

maybeGetClassOpId :: GHC.IdDetails -> Maybe GHC.Class
#if __GLASGOW_HASKELL__ >= 912
maybeGetClassOpId (GHC.ClassOpId cls _) = Just cls
maybeGetClassOpId _ = Nothing
#else
maybeGetClassOpId (GHC.ClassOpId cls) = Just cls
maybeGetClassOpId _ = Nothing
#endif
