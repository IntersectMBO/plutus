{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- | An on-chain numeric type representing a ratio of non-negative numbers.
 = Warning
 This is an internal module; as such, it exposes the 'NatRatio'
 implementation, which can be used to violate constraints if used without
 care. This module primarily exists to support @testlib@, or for some internal
 APIs; if at all possible, use 'PlutusTx.NatRatio' instead.
-}
module PlutusTx.NatRatio.Internal (
  NatRatio (..),
  natRatio,
  fromNatural,
  numerator,
  denominator,
  truncate,
  PlutusTx.NatRatio.Internal.round,
  properFraction,
) where

import           Control.Monad             (guard)
import           Data.Aeson                (FromJSON (parseJSON), ToJSON)
import           PlutusTx.IsData.Class     (FromData (fromBuiltinData), ToData, UnsafeFromData (unsafeFromBuiltinData))
import           PlutusTx.Lift             (makeLift)
import           PlutusTx.Natural.Internal (Natural (Natural))
import           PlutusTx.Numeric.Class
import           PlutusTx.Prelude
import qualified PlutusTx.Ratio            as Ratio
import qualified Prelude

{- | A ratio of 'Natural's. Similar to 'Rational', but with the numerator and
 denominator guaranteed non-negative.
-}
newtype NatRatio = NatRatio Rational
  deriving stock (Prelude.Show)
  deriving
    ( Prelude.Eq
    , Eq
    , Ord
    , AdditiveSemigroup
    , AdditiveMonoid
    , MultiplicativeSemigroup
    , MultiplicativeMonoid
    , ToData
    , ToJSON
    )
    via Rational

instance FromJSON NatRatio where
  parseJSON v = do
    r <- parseJSON v
    guard (r >= zero)
    Prelude.pure . NatRatio $ r

instance FromData NatRatio where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData dat = case fromBuiltinData dat of
    Nothing -> Nothing
    Just r ->
      if natAbs r == r
        then Just (NatRatio r)
        else Nothing

instance UnsafeFromData NatRatio where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData dat =
    let r = unsafeFromBuiltinData dat
     in if natAbs r == r
          then NatRatio r
          else error . trace "Negative fractions cannot be NatRatio" $ ()

-- | 'NatRatio' monus is \'difference-or-zero\'.
instance AdditiveHemigroup NatRatio where
  {-# INLINEABLE (^-) #-}
  NatRatio r1 ^- NatRatio r2
    | r1 < r2 = zero
    | otherwise = NatRatio $ r1 - r2

instance MultiplicativeGroup NatRatio where
  {-# INLINEABLE (/) #-}
  NatRatio r / NatRatio r' = NatRatio (r / r')
  {-# INLINEABLE reciprocal #-}
  reciprocal (NatRatio r) = NatRatio . Ratio.recip $ r


-- | Safely construct a 'NatRatio'. Checks for a zero denominator.
{-# INLINEABLE natRatio #-}
natRatio :: Natural -> Natural -> Maybe NatRatio
natRatio (Natural n) (Natural m) =
  if m == 0
    then Nothing
    else Just . NatRatio $ n Ratio.% m

-- | Convert a 'Natural' into a 'NatRatio' with the same value.
{-# INLINEABLE fromNatural #-}
fromNatural :: Natural -> NatRatio
fromNatural (Natural n) = NatRatio . fromInteger $ n

-- | Retrieve the numerator of a 'NatRatio'.
{-# INLINEABLE numerator #-}
numerator :: NatRatio -> Natural
numerator (NatRatio r) = Natural . Ratio.numerator $ r

{- | Retrieve the denominator of a 'NatRatio'. This is guaranteed non-zero,
 though the result type doesn't specify this.
-}
{-# INLINEABLE denominator #-}
denominator :: NatRatio -> Natural
denominator (NatRatio r) = Natural . Ratio.denominator $ r

-- | Round the 'NatRatio' down.
{-# INLINEABLE truncate #-}
truncate :: NatRatio -> Natural
truncate (NatRatio r) = Natural . Ratio.truncate $ r

-- | Round the 'NatRatio' arithmetically.
{-# INLINEABLE round #-}
round :: NatRatio -> Natural
round (NatRatio r) = Natural . Ratio.round $ r

{- | Separate a 'NatRatio' into a whole and a fractional part, such that the
 fractional part is guaranteed to be less than @1@.
-}
{-# INLINEABLE properFraction #-}
properFraction :: NatRatio -> (Natural, NatRatio)
properFraction (NatRatio r) =
  let (n, r') = Ratio.properFraction r
   in (Natural n, NatRatio r')

instance IntegralDomain Rational NatRatio where
  {-# INLINEABLE abs #-}
  abs = natAbs
  {-# INLINEABLE signum #-}
  signum x
    | x == zero = zero
    | x < zero = negate one
    | otherwise = one
  {-# INLINEABLE projectAbs #-}
  projectAbs = NatRatio . natAbs
  {-# INLINEABLE restrictMay #-}
  restrictMay x
    | x < zero = Nothing
    | otherwise = Just . NatRatio $ x
  {-# INLINEABLE addExtend #-}
  addExtend (NatRatio r) = r

makeLift ''NatRatio
