{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

{-# HLINT ignore #-}

module BuiltinCasing.Lib
  ( useTwiceData
  , useTwiceByteString
  , useTwiceString
  ) where

import PlutusTx
import PlutusTx.Builtins.Internal (unitval)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude

{-| Regression tests for #7716.  The simplifier unwraps single-constructor
opaque types via case-of-known-constructor, potentially exposing inner types
(Data, ByteString, Text) in join point type signatures.  Without the second
constructor (see Note [Opaque builtin types]), the plugin with BuiltinCasing
would try to compile the inner type as a regular ADT and crash.

Each test targets a different opaque builtin type:
  - useTwiceData:        BuiltinData       (wraps PlutusCore.Data.Data)
  - useTwiceByteString:  BuiltinByteString (wraps ByteString -> BS Addr#)
  - useTwiceString:      BuiltinString     (wraps Text -> Array# Char#) -}
useTwiceData :: BuiltinData -> BuiltinUnit
useTwiceData bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = Data.List.caseList' Nothing (\(h :: BuiltinData) _t -> Just h)

useTwiceByteString :: BuiltinByteString -> BuiltinUnit
useTwiceByteString bs =
  case BI.appendByteString bs bs of
    _ -> case BI.appendByteString bs bs of
      _ -> unitval

useTwiceString :: BuiltinString -> BuiltinUnit
useTwiceString s =
  case BI.appendString s s of
    _ -> case BI.appendString s s of
      _ -> unitval
