{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

{-# HLINT ignore #-}

module BuiltinCasing.Lib
  ( caseListTwice
  , caseListTwiceByteString
  ) where

import PlutusTx
import PlutusTx.Builtins.Internal (BuiltinByteString, BuiltinUnit, unitval)
import PlutusTx.Data.List (caseList')
import PlutusTx.Prelude

{-| Regression tests for #7716.  Calling caseList' twice on the same value
makes GHC's simplifier create a join point whose type exposes the raw
inner type of the opaque builtin wrapper.  Without the second constructor
(see Note [Opaque builtin types]), the plugin with BuiltinCasing would try
to compile the inner type as an ADT and crash on Addr#.

Each test below targets a different opaque builtin type:
  - caseListTwice:           BuiltinData       (wraps PlutusCore.Data.Data)
  - caseListTwiceByteString: BuiltinByteString  (wraps ByteString -> BS Addr#) -}
caseListTwice :: BuiltinData -> BuiltinUnit
caseListTwice bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = caseList' Nothing (\(h :: BuiltinData) _t -> Just h)

caseListTwiceByteString :: BuiltinData -> BuiltinUnit
caseListTwiceByteString bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = caseList' Nothing (\(h :: BuiltinByteString) _t -> Just h)
