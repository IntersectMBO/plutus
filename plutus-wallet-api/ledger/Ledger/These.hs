{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.These(
    These(..)
  , these
  , theseWithDefault
  ) where

-- | A 'These' @a@ @b@ is either an @a@, or a @b@ or an @a@ and a @b@.
-- Plutus version of 'Data.These'.
data These a b = This a | That b | These a b

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
