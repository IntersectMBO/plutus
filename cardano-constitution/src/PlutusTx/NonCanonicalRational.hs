{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
-- editorconfig-checker-disable-file
{-# LANGUAGE NoImplicitPrelude #-}

-- | Same representation as Tx.Ratio but uses a different BuiltinData encoding
module PlutusTx.NonCanonicalRational
  ( NonCanonicalRational (..)
  ) where

import PlutusTx as Tx
import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Ratio as Tx
import PlutusTx.Trace (traceError)

-- We agreed to have a different BuiltinData encoding for Rationals for the ConstitutionScript,
-- other than the canonical encoding for datatypes.
-- This wrapper overloads the ToData to this agreed-upon encoding, for testing and benchmarking.
newtype NonCanonicalRational = NonCanonicalRational Tx.Rational

instance ToData NonCanonicalRational where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (NonCanonicalRational tx) =
    let num = Tx.numerator tx
        den = Tx.denominator tx
     in toBuiltinData [num, den]

instance UnsafeFromData NonCanonicalRational where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData (BI.unsafeDataAsList -> bl) =
    -- this is the fastest way I found to convert to Rational
    let bl' = BI.tail bl
     in BI.ifThenElse
          (BI.null (BI.tail bl'))
          (\() -> NonCanonicalRational (Tx.unsafeRatio (B.unsafeDataAsI (BI.head bl)) (B.unsafeDataAsI (BI.head bl'))))
          (\() -> traceError "A Rational had too many list components")
          ()
