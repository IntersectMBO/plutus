{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.These where

-- | A 'These' @a@ @b@ is either an @a@, or a @b@ or an @a@ and a @b@.
-- Plutus version of 'Data.These'.
data These a b = This a | That b | These a b

{-# INLINABLE theseWithDefault #-}
-- | Consume a 'These a b' value.
theseWithDefault :: a -> b -> (a -> b -> c) -> These a b -> c
theseWithDefault a' b' f = \case
    This a -> f a b'
    That b -> f a' b
    These a b -> f a b

{-# INLINABLE these #-}
these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these f g h = \case
    This a -> f a
    That b -> g b
    These a b -> h a b

{-# INLINABLE mergeThese #-}
mergeThese :: (a -> a -> a) -> These a a -> a
mergeThese = these (\a -> a) (\a -> a)

{-# INLINABLE andDefinitely #-}
andDefinitely :: Maybe a -> b -> These a b
andDefinitely ma b = case ma of
    Just a -> These a b
    Nothing -> That b

{-# INLINABLE andMaybe #-}
andMaybe :: a -> Maybe b -> These a b
andMaybe a mb = case mb of
    Just b -> These a b
    Nothing -> This a
