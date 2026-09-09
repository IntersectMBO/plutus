{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module PlutusLedgerApi.V4.Ratio
  ( Rational (..)
  , ratio
  , unsafeRatio
  , numerator
  , denominator
  , fromHaskellRatio
  , toHaskellRatio
  , fromGHC
  , toGHC
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Ratio qualified as Haskell
import GHC.Generics (Generic)
import PlutusLedgerApi.V4.Internal (ListEncoded (..))
import PlutusTx qualified
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..))
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio qualified as Ratio
import Prettyprinter (Pretty)
import Prelude hiding (Rational)

newtype Rational = Rational {unRational :: Ratio.Rational}
  deriving stock (Generic)
  deriving newtype
    ( Eq
    , Ord
    , Show
    , Pretty
    , ToJSON
    , FromJSON
    , PlutusTx.Eq
    , PlutusTx.Ord
    , PlutusTx.Enum
    , PlutusTx.AdditiveSemigroup
    , PlutusTx.AdditiveMonoid
    , PlutusTx.AdditiveGroup
    , PlutusTx.MultiplicativeSemigroup
    , PlutusTx.MultiplicativeMonoid
    , PlutusTx.Module Integer
    )
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded Ratio.Rational

instance HasBlueprintDefinition Rational where
  type Unroll Rational = '[Rational, Integer]

instance HasBlueprintSchema Ratio.Rational referencedTypes => HasBlueprintSchema Rational referencedTypes where
  schema = schema @(ListEncoded Ratio.Rational) @referencedTypes

PlutusTx.makeLift ''Rational

{-# INLINEABLE ratio #-}
ratio :: Integer -> Integer -> Maybe Rational
ratio numeratorValue denominatorValue =
  Rational PlutusTx.<$> Ratio.ratio numeratorValue denominatorValue

{-# INLINEABLE unsafeRatio #-}
unsafeRatio :: Integer -> Integer -> Rational
unsafeRatio numeratorValue denominatorValue = Rational (Ratio.unsafeRatio numeratorValue denominatorValue)

{-# INLINEABLE numerator #-}
numerator :: Rational -> Integer
numerator (Rational value) = Ratio.numerator value

{-# INLINEABLE denominator #-}
denominator :: Rational -> Integer
denominator (Rational value) = Ratio.denominator value

fromHaskellRatio :: Haskell.Rational -> Rational
fromHaskellRatio value = Rational (Ratio.fromHaskellRatio value)

toHaskellRatio :: Rational -> Haskell.Rational
toHaskellRatio (Rational value) = Ratio.toHaskellRatio value

fromGHC :: Haskell.Rational -> Rational
fromGHC = fromHaskellRatio

toGHC :: Rational -> Haskell.Rational
toGHC = toHaskellRatio
