{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

{-# HLINT ignore #-}

module BuiltinCasing.Lib (caseListTwice) where

import PlutusTx
import PlutusTx.Builtins.Internal (unitval)
import PlutusTx.Data.List (caseList')
import PlutusTx.Prelude

{-| Regression test for #7716.  Calling caseList' twice on the same value
makes GHC's simplifier create a join point whose type exposes the raw
PlutusCore.Data.Data inside BuiltinData.  Without the second constructor
on BuiltinData (see Note [Opaque builtin types]), the plugin with
BuiltinCasing would try to compile Data as an ADT and crash on Addr#. -}
caseListTwice :: BuiltinData -> BuiltinUnit
caseListTwice bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = caseList' Nothing (\(h :: BuiltinData) _t -> Just h)
