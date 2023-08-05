{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
{-# OPTIONS_GHC -fomit-interface-pragmas #-}
module PlutusTx.Plugin.Utils where

import Data.Proxy
import GHC.TypeLits
import PlutusTx.Code
import PlutusTx.Utils

{- Note [plc and Proxy]
It would be nice to use TypeApplications instead of passing a Proxy to plc.
However, this means we need to create a type application in the TH-generated code which calls it.
As of recent versions of GHC, this causes an error in the module where the splice appears if it
doesn't have TypeApplications enabled.

Generally we want to avoid forcing users to enable language extensions, so we use
a Proxy to avoid this.
-}

-- This needs to be defined here so we can reference it in the TH functions.
-- If we inline this then we won't be able to find it later!
{-# NOINLINE plc #-}
-- | Marks the given expression for compilation to PLC.
plc :: forall (loc::Symbol) a . Proxy loc -> a -> CompiledCode a
-- this constructor is only really there to get rid of the unused warning
plc _ _ = SerializedCode (mustBeReplaced "plc") (mustBeReplaced "pir") (mustBeReplaced "covidx")
