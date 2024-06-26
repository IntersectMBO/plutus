-- editorconfig-checker-disable-file
-- | Same representation as Tx.Ratio but uses a different BuiltinData encoding
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module PlutusTx.NonCanonicalRational
    ( NonCanonicalRational (..)
    ) where

import PlutusTx as Tx
import PlutusTx.Builtins as B
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Ratio as Tx

-- We agreed to have a different BuiltinData encoding for Rationals for the ConstitutionScript,
-- other than the canonical encoding for datatypes.
-- This wrapper overloads the ToData to this agreed-upon encoding, for testing and benchmarking.
newtype NonCanonicalRational = NonCanonicalRational Tx.Rational

instance ToData NonCanonicalRational where
  {-# INLINABLE toBuiltinData #-}
  toBuiltinData (NonCanonicalRational tx) =
    let num = Tx.numerator tx
        den = Tx.denominator tx
    in toBuiltinData [num,den]

instance UnsafeFromData NonCanonicalRational where
  {-# INLINABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData (BI.unsafeDataAsList -> bl) =
        -- this is the fastest way I found to convert to Rational
        let bl' = BI.tail bl
        in BI.ifThenElse (BI.null (BI.tail bl'))
            (\() -> NonCanonicalRational (Tx.unsafeRatio (B.unsafeDataAsI (BI.head bl)) (B.unsafeDataAsI (BI.head bl'))))
            (\() -> BI.trace "A Rational had too many list components" (B.error ()))
           ()
