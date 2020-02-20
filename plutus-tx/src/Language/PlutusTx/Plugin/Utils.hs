{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module Language.PlutusTx.Plugin.Utils where

import           GHC.TypeLits
import           Language.PlutusTx.Code
import           Language.PlutusTx.Utils

import qualified Language.PlutusCore.Universe as PLC

-- This needs to be defined here so we can reference it in the TH functions.
-- If we inline this then we won't be able to find it later!
{-# NOINLINE plc #-}
-- | Marks the given expression for compilation to PLC.
plc :: forall (loc::Symbol) a . a -> CompiledCode PLC.DefaultUni a
-- this constructor is only really there to get rid of the unused warning
plc _ = SerializedCode (mustBeReplaced "plc") (mustBeReplaced "pir")
