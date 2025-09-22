{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

#if __GLASGOW_HASKELL__ >= 914
-- The `ghc-9.14` alpha release has what looks like a bug;
-- https://gitlab.haskell.org/ghc/ghc/-/issues/26381
{-# OPTIONS_GHC -Wno-redundant-constraints  #-}
#endif

module PlutusTx.These (
  These (..),
  these,
  theseWithDefault,
) where

import GHC.Generics (Generic)
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition)
import Prelude qualified as Haskell

{-| A 'These' @a@ @b@ is either an @a@, or a @b@ or an @a@ and a @b@.
Plutus version of 'Data.These'.
-}
data These a b = This a | That b | These a b
  deriving stock (Generic, Haskell.Eq, Haskell.Show)
  deriving anyclass (HasBlueprintDefinition)

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
