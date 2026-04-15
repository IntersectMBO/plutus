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
  , caseListTwiceString
  ) where

import PlutusTx
import PlutusTx.Builtins.Internal
  ( BuiltinByteString
  , BuiltinList
  , BuiltinString
  , BuiltinUnit
  , caseList'
  , unitval
  )
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude

{-| Regression tests for #7716.  Calling caseList' twice on the same value
makes GHC's simplifier create a join point whose type exposes the raw
inner type of the opaque builtin wrapper.  Without the second constructor
(see Note [Opaque builtin types]), the plugin with BuiltinCasing would try
to compile the inner type as an ADT and crash on Addr#.

Each test targets a different opaque builtin type:
  - caseListTwice:           BuiltinData       (wraps PlutusCore.Data.Data)
  - caseListTwiceByteString: BuiltinByteString  (wraps ByteString -> BS Addr#)
  - caseListTwiceString:     BuiltinString      (wraps Text -> Array# Char#) -}
caseListTwice :: BuiltinData -> BuiltinUnit
caseListTwice bd =
  case toBuiltinData (firstOf items) of
    _ -> case toBuiltinData (firstOf items) of
      _ -> unitval
  where
    items = unsafeFromBuiltinData bd
    firstOf = Data.List.caseList' Nothing (\(h :: BuiltinData) _t -> Just h)

caseListTwiceByteString :: BuiltinList BuiltinByteString -> BuiltinUnit
caseListTwiceByteString items =
  case firstOf items of
    Nothing -> case firstOf items of
      Nothing -> unitval
      Just _ -> unitval
    Just _ -> case firstOf items of
      Nothing -> unitval
      Just _ -> unitval
  where
    firstOf = caseList' Nothing (\(h :: BuiltinByteString) _ -> Just h)

caseListTwiceString :: BuiltinList BuiltinString -> BuiltinUnit
caseListTwiceString items =
  case firstOf items of
    Nothing -> case firstOf items of
      Nothing -> unitval
      Just _ -> unitval
    Just _ -> case firstOf items of
      Nothing -> unitval
      Just _ -> unitval
  where
    firstOf = caseList' Nothing (\(h :: BuiltinString) _ -> Just h)
