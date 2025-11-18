{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module UntypedPlutusCore.Evaluation.Machine.Cek.StepCounter where

import Control.Monad.Primitive
import Data.Coerce (coerce)
import Data.Kind
import Data.Primitive qualified as P
import Data.Proxy
import Data.Word
import GHC.TypeNats (KnownNat, Nat, natVal, type (-))

-- See Note [Step counter data structure]
-- You might think that since we can store whatever we like in here we might as well
-- use machine words (i.e. 'Word64'), but that is actually slower.
{-| A set of 'Word8' counters that is used in the CEK machine
to count steps. -}
newtype StepCounter (n :: Nat) s = StepCounter (P.MutablePrimArray s Word8)

-- | Make a new 'StepCounter' with the given number of counters.
newCounter :: (KnownNat n, PrimMonad m) => Proxy n -> m (StepCounter n (PrimState m))
newCounter p = do
  let sz = fromIntegral $ natVal p
  c <- StepCounter <$> P.newPrimArray sz
  resetCounter c
  pure c
{-# INLINE newCounter #-}

-- | Reset all the counters in the given 'StepCounter' to zero.
resetCounter :: forall n m. (KnownNat n, PrimMonad m) => StepCounter n (PrimState m) -> m ()
resetCounter (StepCounter arr) =
  let sz = fromIntegral $ natVal (Proxy @n)
   in P.setPrimArray arr 0 sz 0
{-# INLINE resetCounter #-}

-- | Read the value of a counter.
readCounter :: forall m n. PrimMonad m => StepCounter n (PrimState m) -> Int -> m Word8
readCounter =
  coerce
    @(P.MutablePrimArray (PrimState m) Word8 -> Int -> m Word8)
    @(StepCounter n (PrimState m) -> Int -> m Word8)
    P.readPrimArray
{-# INLINE readCounter #-}

-- | Write to a counter.
writeCounter
  :: forall m n
   . PrimMonad m
  => StepCounter n (PrimState m)
  -> Int
  -> Word8
  -> m ()
writeCounter =
  coerce
    @(P.MutablePrimArray (PrimState m) Word8 -> Int -> Word8 -> m ())
    @(StepCounter n (PrimState m) -> Int -> Word8 -> m ())
    P.writePrimArray
{-# INLINE writeCounter #-}

-- | Modify the value of a counter. Returns the modified value.
modifyCounter
  :: PrimMonad m
  => Int
  -> (Word8 -> Word8)
  -> StepCounter n (PrimState m)
  -> m Word8
modifyCounter i f c = do
  v <- readCounter c i
  let modified = f v
  writeCounter c i modified
  pure modified
{-# INLINE modifyCounter #-}

-- | The type of natural numbers in Peano form.
data Peano
  = Z
  | S Peano

type NatToPeano :: Nat -> Peano
type family NatToPeano n where
  NatToPeano 0 = 'Z
  NatToPeano n = 'S (NatToPeano (n - 1))

type UpwardsM :: (Type -> Type) -> Peano -> Constraint
class Applicative f => UpwardsM f n where
  {-| @upwardsM i k@ means @k i *> k (i + 1) *> ... *> k (i + n - 1)@.
  We use this function in order to statically unroll a loop in 'itraverseCounter_' through
  instance resolution. This makes @validation@ benchmarks a couple of percent faster. -}
  upwardsM :: Int -> (Int -> f ()) -> f ()

instance Applicative f => UpwardsM f 'Z where
  upwardsM _ _ = pure ()
  {-# INLINE upwardsM #-}

instance UpwardsM f n => UpwardsM f ('S n) where
  upwardsM !i k = k i *> upwardsM @f @n (i + 1) k
  {-# INLINE upwardsM #-}

-- | Traverse the counters with an effectful function.
itraverseCounter_
  :: forall n m
   . (UpwardsM m (NatToPeano n), PrimMonad m)
  => (Int -> Word8 -> m ())
  -> StepCounter n (PrimState m)
  -> m ()
itraverseCounter_ f (StepCounter arr) = do
  -- The safety of this operation is a little subtle. The frozen array is only
  -- safe to use if the underlying mutable array is not mutated 'afterwards'.
  -- In our case it likely _will_ be mutated afterwards... but not until we
  -- are done with the frozen version. That ordering is enforced by the fact that
  -- the whole thing runs in 'm': future accesses to the mutable array can't
  -- happen until this whole function is finished.
  arr' <- P.unsafeFreezePrimArray arr
  upwardsM @_ @(NatToPeano n) 0 $ \i -> f i $ P.indexPrimArray arr' i
{-# INLINE itraverseCounter_ #-}

-- | Traverse the counters with an effectful function.
iforCounter_
  :: (UpwardsM m (NatToPeano n), PrimMonad m)
  => StepCounter n (PrimState m)
  -> (Int -> Word8 -> m ())
  -> m ()
iforCounter_ = flip itraverseCounter_
{-# INLINE iforCounter_ #-}

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
