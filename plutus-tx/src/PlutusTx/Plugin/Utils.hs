{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
{-# OPTIONS_GHC -fomit-interface-pragmas #-}

module PlutusTx.Plugin.Utils where

import GHC.TypeLits
import PlutusTx.Code
import PlutusTx.Utils

-- This needs to be defined here so we can reference it in the TH functions.
-- If we inline this then we won't be able to find it later!

-- | Marker recognised by the plugin. The TH 'compile' wraps it with
-- @anchor \@\"…\"@ to attach the splice's source location; direct (non-TH)
-- callers can use it bare and rely on the typecheck plugin to anchor it.
plinthc :: forall a. a -> CompiledCode a
plinthc _ = SerializedCode (mustBeReplaced "plc") (mustBeReplaced "pir") (mustBeReplaced "covidx")
{-# OPAQUE plinthc #-}

{-| This function is used in `typeCheckResultAction` to mark the given expression
with its source location. -}
anchor :: forall (loc :: Symbol) a. a -> a
anchor a = a
{-# OPAQUE anchor #-}

{-| This function is used in `typeCheckResultAction` to mark the given expression
as unsupported by Plinth. -}
unsupported :: forall (err :: Symbol) (loc :: Symbol) a. a -> a
unsupported x = x
{-# OPAQUE unsupported #-}
