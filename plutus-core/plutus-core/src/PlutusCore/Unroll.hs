{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-| Static loop unrolling utilities using type-level Peano numbers.

This module provides utilities for statically unrolling loops at compile time.
GHC resolves the type class instances at compile time, resulting in unrolled
code that avoids runtime overhead.

See Note [Static loop unrolling] for details on the technique. -}
module PlutusCore.Unroll
  ( -- * Peano numbers
    Peano (..)
  , NatToPeano

    -- * Statically unrolled list drop
  , Drop (..)
  , dropN

    -- * Statically unrolled effectful iteration
  , UpwardsM (..)
  ) where

import Data.Kind (Constraint, Type)
import GHC.TypeNats (Nat, type (-))

{- Note [Static loop unrolling]
To avoid runtime loop overhead, we use type-level Peano numbers to guide instance
resolution. GHC resolves the instances at compile time and unrolls the loop into
straight-line code.

For example, 'dropN @3' becomes pattern matching equivalent to:
  case xs of
    (_:_:_:rest) -> Just rest
    _ -> Nothing

And 'upwardsM @_ @(NatToPeano 3) 0 k' becomes:
  k 0 *> k 1 *> k 2

Benefits:
1. No runtime recursion overhead
2. No allocations for intermediate structures
3. GHC can optimize the unrolled code very well
4. Instance resolution happens entirely at compile time

The technique was originally used in the CEK machine step counter:
https://github.com/IntersectMBO/plutus/pull/5265
-}

--------------------------------------------------------------------------------
-- Peano numbers ---------------------------------------------------------------

-- | Peano representation of natural numbers for type-level recursion.
data Peano = Z | S Peano

-- | Convert a type-level 'Nat' to 'Peano' form for instance resolution.
type family NatToPeano (n :: Nat) :: Peano where
  NatToPeano 0 = 'Z
  NatToPeano n = 'S (NatToPeano (n - 1))

--------------------------------------------------------------------------------
-- Statically unrolled list drop -----------------------------------------------

{-| Statically unrolled drop: drops exactly @n@ elements if possible.
Returns 'Nothing' if the list has fewer than @n@ elements.

The @n@ parameter is a 'Peano' number that guides instance resolution.
Use 'dropN' for a more convenient interface with 'Nat' literals. -}
class Drop (n :: Peano) where
  drop' :: [a] -> Maybe [a]

instance Drop 'Z where
  drop' = Just
  {-# INLINE drop' #-}

instance Drop n => Drop ('S n) where
  drop' [] = Nothing
  drop' (_ : xs) = drop' @n xs
  {-# INLINE drop' #-}

{-| Drop exactly @n@ elements from a list, returning 'Nothing' if too short.

The drop count is statically unrolled at compile time via instance resolution.

@
dropN \@3 [1,2,3,4,5] == Just [4,5]
dropN \@3 [1,2]       == Nothing
@ -}
dropN :: forall n a. Drop (NatToPeano n) => [a] -> Maybe [a]
dropN = drop' @(NatToPeano n)
{-# INLINE dropN #-}

--------------------------------------------------------------------------------
-- Statically unrolled effectful iteration -------------------------------------

{-| Statically unrolled effectful iteration over a range.

@upwardsM i k@ means @k i *> k (i + 1) *> ... *> k (i + n - 1)@.

We use this to statically unroll loops through instance resolution.
This makes validation benchmarks a couple of percent faster. -}
type UpwardsM :: (Type -> Type) -> Peano -> Constraint
class Applicative f => UpwardsM f n where
  upwardsM :: Int -> (Int -> f ()) -> f ()

instance Applicative f => UpwardsM f 'Z where
  upwardsM _ _ = pure ()
  {-# INLINE upwardsM #-}

instance UpwardsM f n => UpwardsM f ('S n) where
  upwardsM !i k = k i *> upwardsM @f @n (i + 1) k
  {-# INLINE upwardsM #-}
