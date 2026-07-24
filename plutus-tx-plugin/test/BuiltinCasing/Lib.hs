{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

{-# HLINT ignore "Redundant case" #-}

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

{-| Regression tests for #7716; see Note [Transparent BuiltinData] in
PlutusTx.Compiler.Expr.  Only useTwiceData reproduces the crash shape — its
golden contains a join point.  useTwiceByteString and useTwiceString are
canaries pinning that those wrappers never unwrap. -}
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
