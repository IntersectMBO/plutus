-- EXPERIMENT ONLY. The evaluator owns its active environment; continuations
-- borrow prefixes in LIFO order, and escaping values permanently seal prefixes.
-- A slot may be overwritten only above BOTH barriers. This does not attempt
-- to reclaim a sealed prefix after its last closure dies.
-- RealWorld is an experimental bridge to the public, state-free CekValue type.
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.ArrayEnv where

import Data.Primitive.PrimArray
import Data.Primitive.SmallArray
import Data.Word (Word64)
import GHC.Exts (IsList (..), RealWorld)
import System.IO.Unsafe (unsafePerformIO, unsafeDupablePerformIO)
import UntypedPlutusCore.Core.Type qualified as U

-- Metadata: slot 0 = permanent barrier, slot 1 = dynamic barrier.
-- The final field is the previous dynamic barrier, or -1 for an active handle.
data RAList a
  = Empty {-# UNPACK #-} !Int
  | ArrayEnv {-# UNPACK #-} !Int {-# UNPACK #-} !Int
      !(SmallMutableArray RealWorld a) !(MutablePrimArray RealWorld Int)
      {-# UNPACK #-} !Int

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

newMetadata :: IO (MutablePrimArray RealWorld Int)
newMetadata = do
  m <- newPrimArray 2
  setPrimArray m 0 2 0
  pure m
{-# INLINE newMetadata #-}

-- This entry point is persistent, including concurrent callers. It always
-- copies and seals the result; it is used by the steppable evaluator/IsList.
cons :: a -> RAList a -> RAList a
cons x e = unsafePerformIO $ do
  result <- copyConsM x e
  sealM result
{-# NOINLINE cons #-}

copyConsM :: a -> RAList a -> IO (RAList a)
copyConsM x e = case e of
  Empty capacity -> do
    a <- newSmallArray (max 1 capacity) (error "uninitialized slot")
    writeSmallArray a 0 x
    m <- newMetadata
    pure (ArrayEnv 1 capacity a m (-1))
  ArrayEnv n capacity a _ _ -> do
    let size = if capacity == 0 then n + 1 else capacity
    if n >= size then error "array environment capacity exceeded" else do
      b <- newSmallArray size (error "uninitialized slot")
      copySmallMutableArray b 0 a 0 n
      writeSmallArray b n x
      m <- newMetadata
      pure (ArrayEnv (n + 1) capacity b m (-1))
{-# INLINE copyConsM #-}

-- Only the sequential CEK engine may call the borrowing/mutable API.
consM :: a -> RAList a -> IO (RAList a)
consM x e = case e of
  Empty _ -> copyConsM x e
  ArrayEnv n capacity a m _ -> do
    sealed <- readPrimArray m 0
    borrowed <- readPrimArray m 1
    if n < sealed || n < borrowed || n >= sizeofSmallMutableArray a
      then copyConsM x e
      else do
        writeSmallArray a n x
        pure (ArrayEnv (n + 1) capacity a m (-1))
{-# INLINE consM #-}

-- All actual closures must be sealed BEFORE they can enter a value/context,
-- a builtin runtime, or a lazy discharge/error term.
sealM :: RAList a -> IO (RAList a)
sealM e = case e of
  Empty _ -> pure e
  ArrayEnv n _ _ m _ -> do
    old <- readPrimArray m 0
    if n > old then writePrimArray m 0 n else pure ()
    pure e
{-# INLINE sealM #-}

pinM :: RAList a -> IO (RAList a)
pinM e = case e of
  Empty _ -> pure e
  ArrayEnv n capacity a m _ -> do
    old <- readPrimArray m 1
    writePrimArray m 1 (max old n)
    pure (ArrayEnv n capacity a m old)
{-# INLINE pinM #-}

unpinM :: RAList a -> IO (RAList a)
unpinM e = case e of
  Empty _ -> pure e
  ArrayEnv n capacity a m old
    | old < 0 -> error "unpin of active environment"
    | otherwise -> do
        writePrimArray m 1 old
        pure (ArrayEnv n capacity a m (-1))
{-# INLINE unpinM #-}

-- Active reads must execute in the machine monad before a later overwrite.
indexOneM :: RAList a -> Word64 -> IO (Maybe a)
indexOneM (Empty _) _ = pure Nothing
indexOneM (ArrayEnv n _ a _ _) i
  | i == 0 || i > fromIntegral n = pure Nothing
  | otherwise = do
      !x <- readSmallArray a (n - fromIntegral i)
      pure (Just x)
{-# INLINE indexOneM #-}

-- Pure reads are reserved for permanently sealed snapshots (discharge,
-- steppable evaluation, and persistent representation checks).
contIndexOne :: b -> (a -> b) -> RAList a -> Word64 -> b
contIndexOne z f e i = case unsafeDupablePerformIO (indexOneM e i) of
  Nothing -> z
  Just x -> f x
{-# INLINE contIndexOne #-}

indexOne :: RAList a -> Word64 -> Maybe a
indexOne e i = contIndexOne Nothing Just e i
{-# INLINE indexOne #-}

instance IsList (RAList a) where
  type Item (RAList a) = a
  fromList = foldr cons empty
  toList (Empty _) = []
  toList e@(ArrayEnv n _ _ _ _) =
    [contIndexOne (error "impossible index") id e (fromIntegral i) | i <- [1 .. n]]

instance Show a => Show (RAList a) where
  showsPrec d = showsPrec d . toList
