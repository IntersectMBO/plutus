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

{-| Regression tests for #7716.  GHC's unboxing of a single-constructor opaque
wrapper can expose its inner type in join point type signatures, which the
plugin with BuiltinCasing then tries to compile as a regular ADT, crashing on
primitives like Addr#.

Only useTwiceData reproduces that shape — its golden contains a join point,
kept compilable by BuiltinData's second constructor (see
Note [Opaque builtin types]).  useTwiceByteString and useTwiceString are
canaries: their goldens pin that these wrappers are never unwrapped in the
first place (all their operations are OPAQUE), so a change in that behaviour
surfaces as a golden diff or compile error. -}
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
