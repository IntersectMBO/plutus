{-# LANGUAGE ConstraintKinds #-}

module PlutusCore.Compiler.Types where

import Data.Hashable
import PlutusCore.Builtin
import PlutusCore.Default qualified as PLC
import PlutusCore.Name.Unique
import PlutusCore.Quote
import UntypedPlutusCore.Core.Type qualified as UPLC

-- TODO1: move somewhere more appropriate?
-- TODO2: we probably don't want this in memory so after MVP
-- we should consider serializing this to disk
newtype UPLCSimplifierTrace name uni fun a =
  UPLCSimplifierTrace
    { uplcSimplifierTrace
      :: [UPLC.Term name uni fun a]
    }

initUPLCSimplifierTrace :: UPLCSimplifierTrace name uni fun a
initUPLCSimplifierTrace = UPLCSimplifierTrace []

type Compiling m uni fun name a =
  ( ToBuiltinMeaning uni fun
  , MonadQuote m
  , HasUnique name TermUnique
  , Ord name
  , Typeable name
  , Hashable fun
  )
