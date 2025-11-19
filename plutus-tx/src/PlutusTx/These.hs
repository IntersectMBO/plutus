{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module PlutusTx.These
  ( These (..)
  , these
  , theseWithDefault
  ) where

import GHC.Generics (Generic)
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition, definitionRef)
import PlutusTx.Blueprint.TH (makeIsDataSchemaIndexed)
import PlutusTx.Eq
import PlutusTx.Lift
import PlutusTx.Ord
import PlutusTx.Show
import Prelude qualified as Haskell

{-| A 'These' @a@ @b@ is either an @a@, or a @b@ or an @a@ and a @b@.
Plutus version of 'Data.These'. -}
data These a b = This a | That b | These a b
  deriving stock (Generic, Haskell.Eq, Haskell.Show)
  deriving anyclass (HasBlueprintDefinition)

deriveEq ''These
deriveShow ''These
makeLift ''These
makeIsDataSchemaIndexed ''These [('This, 0), ('That, 1), ('These, 2)]

{-# INLINEABLE theseWithDefault #-}

-- | Consume a 'These a b' value.
theseWithDefault :: a -> b -> (a -> b -> c) -> These a b -> c
theseWithDefault a' b' f = \case
  This a -> f a b'
  That b -> f a' b
  These a b -> f a b

these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these f g h = \case
  This a -> f a
  That b -> g b
  These a b -> h a b
{-# INLINEABLE these #-}

instance (Ord a, Ord b) => Ord (These a b) where
  {-# INLINEABLE compare #-}
  compare (This a) (This a') = compare a a'
  compare (That b) (That b') = compare b b'
  compare (These a b) (These a' b') =
    case compare a a' of
      EQ -> compare b b'
      c -> c
  compare (This _) _ = LT
  compare (That _) (This _) = GT
  compare (That _) (These _ _) = LT
  compare (These _ _) (This _) = GT
  compare (These _ _) (That _) = GT
