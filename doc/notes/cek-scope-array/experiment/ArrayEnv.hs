-- EXPERIMENT ONLY: persistent arrays; published arrays are never mutated.
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv where

import Control.Monad.ST (runST)
import Data.Primitive.SmallArray
import Data.Word (Word64)
import GHC.Exts (IsList (..))
import UntypedPlutusCore.Core.Type qualified as U

-- Capacity zero selects exact-length allocation; otherwise every extension
-- allocates the statically determined capacity and copies the live prefix.
data RAList a = ArrayEnv {-# UNPACK #-} !Int {-# UNPACK #-} !Int !(SmallArray a)
  deriving stock (Show)

empty :: RAList a
empty = ArrayEnv 0 0 emptySmallArray
{-# INLINE empty #-}

emptyFor :: U.Term name uni fun ann -> RAList a
emptyFor t = ArrayEnv 0 (maxDepth t) emptySmallArray
{-# INLINE emptyFor #-}

maxDepth :: U.Term name uni fun ann -> Int
maxDepth = go 0
  where
    go !d = \case
      U.LamAbs _ _ t -> go (d + 1) t
      U.Apply _ f x -> max (go d f) (go d x)
      U.Delay _ t -> go d t
      U.Force _ t -> go d t
      U.Constr _ _ ts -> foldr (max . go d) d ts
      U.Case _ t ts -> foldr (max . go d) (go d t) ts
      _ -> d
{-# NOINLINE maxDepth #-}

cons :: a -> RAList a -> RAList a
cons x (ArrayEnv n capacity old) = runST $ do
  let size = if capacity == 0 then n + 1 else capacity
  -- Explicit invariant guard, retained in both checked/unchecked experiments.
  if n >= size then error "array environment capacity exceeded" else do
    new <- newSmallArray size (error "uninitialized environment slot")
    copySmallArray new 0 old 0 n
    writeSmallArray new n x
    ArrayEnv (n + 1) capacity <$> unsafeFreezeSmallArray new
{-# INLINE cons #-}

contIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
contIndexOne z f (ArrayEnv n _ a) i
  | i == 0 || i > fromIntegral n = z
  | otherwise = f (indexSmallArray a (n - fromIntegral i))
{-# INLINE contIndexOne #-}

-- Discharge must remain checked, including for an open lambda returned as a value.
indexOne :: RAList a -> Word64 -> Maybe a
indexOne e i = contIndexOne Nothing Just e i
{-# INLINE indexOne #-}

-- Only called for a term independently proven closed by a FULL scope check.
-- Deliberately not a production API; see the experiment runner's input guard.
uncheckedIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
uncheckedIndexOne _ f (ArrayEnv n _ a) i =
  f (indexSmallArray a (n - fromIntegral i))
{-# INLINE uncheckedIndexOne #-}

instance IsList (RAList a) where
  type Item (RAList a) = a
  fromList = foldr cons empty
  toList (ArrayEnv n _ a) = [indexSmallArray a i | i <- reverse [0 .. n - 1]]
