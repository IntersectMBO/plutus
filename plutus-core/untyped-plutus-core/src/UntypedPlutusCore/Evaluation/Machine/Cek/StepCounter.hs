{-# LANGUAGE BangPatterns #-}
module UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter where

import Control.Monad.Primitive
import Data.Primitive qualified as P
import Data.Word

-- See Note [Step counter data structure]
-- | A set of 'Word8' counters that is used in the CEK machine
-- to count steps.
newtype StepCounter s = StepCounter (P.MutablePrimArray s Word8)

{-# INLINE newCounter #-}
-- | Make a new 'StepCounter' with the given number of counters.
newCounter :: PrimMonad m => Int -> m (StepCounter (PrimState m))
newCounter sz = do
  c <- StepCounter <$> P.newPrimArray sz
  resetCounter c
  pure c

{-# INLINE resetCounter #-}
-- | Reset all the counters in the given 'StepCounter' to zero.
resetCounter :: PrimMonad m => StepCounter (PrimState m) -> m ()
resetCounter (StepCounter arr) = P.setPrimArray arr 0 (P.sizeofMutablePrimArray arr) 0

{-# INLINE readCounter #-}
-- | Read the value of a counter.
readCounter :: PrimMonad m => StepCounter (PrimState m) -> Int -> m Word8
readCounter (StepCounter arr) = P.readPrimArray arr

{-# INLINE writeCounter #-}
-- | Write to a counter.
writeCounter
  :: PrimMonad m
  => StepCounter (PrimState m)
  -> Int
  -> Word8
  -> m ()
writeCounter (StepCounter arr) = P.writePrimArray arr

{-# INLINE modifyCounter #-}
-- | Modify the value of a counter.
modifyCounter
  :: PrimMonad m
  => Int
  -> (Word8 -> Word8)
  -> StepCounter (PrimState m)
  -> m ()
modifyCounter i f c = do
  v <- readCounter c i
  writeCounter c i (f v)

-- I also tried INLINABLE + SPECIALIZE, which just resulted in it getting inlined, so might
-- as well just go straight for that
{-# INLINE itraverseCounter_ #-}
-- | Traverse the counters with an effectful function.
itraverseCounter_ :: (PrimMonad m) => (Int -> Word8 -> m ()) -> StepCounter (PrimState m) -> m ()
itraverseCounter_ f (StepCounter arr) = do
  -- The implementation of this function is very performance-sensitive. I believe
  -- it may be possible to do better, but it's time-consuming to experiment more
  -- and unclear what improves things.

  -- The safety of this operation is a little subtle. The frozen array is only
  -- safe to use if the underlying mutable array is not mutated 'afterwards'.
  -- In our case it likely _will_ be mutated afterwards... but not until we
  -- are done with the frozen version. That ordering is enforced by the fact that
  -- the whole thing runs in 'm': future accesses to the mutable array can't
  -- happen until this whole function is finished.
  arr' <- P.unsafeFreezePrimArray arr
  let
    sz = P.sizeofPrimArray arr'
    go !i
      | i < sz = do
          f i (P.indexPrimArray arr' i)
          go (i+1)
      | otherwise = pure ()
  go 0

{-# INLINE iforCounter_ #-}
-- | Traverse the counters with an effectful function.
iforCounter_ :: (PrimMonad m) => StepCounter (PrimState m) -> (Int -> Word8 -> m ()) -> m ()
iforCounter_ = flip itraverseCounter_

{- Note [Step counter data structure]
The step counter data structure has had several iterations.

Previously we used a "word array", which was a single 'Word64' into which we
packed 8 'Word8's. This worked pretty well: it was pure, and everything reduced
to a bunch of primitive integer operations.

However, it has a key limitation which is that it can only hold 8 counters.
The obvious attempt to expand it to use a 'Word128' performed badly.

The 'PrimArray' approach on the other hand was fairly competitive with the
original 'WordArray', and scales fine to more than 8 counters, so we switched
to using that instead.
-}
