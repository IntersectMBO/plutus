-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Function(
  Bool(..), ($), ($!), (.), id, const, flip, fix, on, asTypeOf, seq, until, (&), applyWhen) where

fix :: forall a . (a -> a) -> a
fix f = f $ fix f

infixl 0 `on`
on :: forall a b c . (a -> a -> b) -> (c -> a) -> (c -> c -> b)
on op sel x y = op (sel x) (sel y)

infixl 1 &
(&) :: forall a b . a -> (a -> b) -> b
(&) x f = f x

applyWhen :: forall a . Bool -> (a -> a) -> a -> a
applyWhen True  f x = f x
applyWhen False _ x = x
