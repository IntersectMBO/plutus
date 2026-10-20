-- EXPERIMENT ONLY: persistent append-only buffers with copying on a fork.
-- The hot path calls consM through the evaluator's ST monad. RealWorld arrays
-- and a pure read wrapper fit the existing public CekValue type; a production
-- implementation should parameterize the environment by the evaluator's state.
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv where

import Data.IORef
import Data.Primitive.SmallArray
import Data.Word (Word64)
import GHC.Exts (IsList (..), RealWorld)
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)
import UntypedPlutusCore.Core.Type qualified as U

-- Every published prefix is immutable. Only its previously unwritten suffix
-- may be filled. Sharing a prefix never grants ownership of a later slot.
data RAList a
  = Empty {-# UNPACK #-} !Int
  | ArrayEnv {-# UNPACK #-} !Int {-# UNPACK #-} !Int
      !(SmallMutableArray RealWorld a) !(IORef Int)

empty :: RAList a
empty = Empty 0
{-# INLINE empty #-}

emptyFor :: U.Term name uni fun ann -> RAList a
emptyFor t = Empty (maxDepth t)
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
cons x e = unsafePerformIO (consM x e)
{-# NOINLINE cons #-}

consM :: a -> RAList a -> IO (RAList a)
consM x e = case e of
  Empty capacity -> do
    a <- newSmallArray (max 1 capacity) (error "uninitialized slot")
    writeSmallArray a 0 x
    cursor <- newIORef 1
    pure (ArrayEnv 1 capacity a cursor)
  ArrayEnv n capacity a cursor -> do
    let size = if capacity == 0 then n + 1 else capacity
    if n >= size then error "array environment capacity exceeded" else do
      -- Atomic ownership claim keeps even independently forced branches safe.
      append <- if n < sizeofSmallMutableArray a
        then atomicModifyIORef' cursor (\h -> if h == n then (n + 1, True) else (h, False))
        else pure False
      if append
        then do
          writeSmallArray a n x
          pure (ArrayEnv (n + 1) capacity a cursor)
        else do
          b <- newSmallArray size (error "uninitialized slot")
          copySmallMutableArray b 0 a 0 n
          writeSmallArray b n x
          cursor' <- newIORef (n + 1)
          pure (ArrayEnv (n + 1) capacity b cursor')
{-# INLINE consM #-}

contIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
contIndexOne z _ (Empty _) _ = z
contIndexOne z f (ArrayEnv n _ a _) i
  | i == 0 || i > fromIntegral n = z
  | otherwise = f (unsafeDupablePerformIO (readSmallArray a (n - fromIntegral i)))
{-# INLINE contIndexOne #-}

indexOne :: RAList a -> Word64 -> Maybe a
indexOne e i = contIndexOne Nothing Just e i
{-# INLINE indexOne #-}

uncheckedIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
uncheckedIndexOne z _ (Empty _) _ = z
uncheckedIndexOne _ f (ArrayEnv n _ a _) i =
  f (unsafeDupablePerformIO (readSmallArray a (n - fromIntegral i)))
{-# INLINE uncheckedIndexOne #-}

instance IsList (RAList a) where
  type Item (RAList a) = a
  fromList = foldr cons empty
  toList (Empty _) = []
  toList e@(ArrayEnv n _ _ _) =
    [contIndexOne (error "impossible index") id e (fromIntegral i) | i <- [1 .. n]]

instance Show a => Show (RAList a) where
  showsPrec d = showsPrec d . toList
