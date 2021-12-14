-- |
-- Module      : Foundation.Array.Mutable
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
module Foundation.Collection.Mutable
    ( MutableCollection(..)
    ) where

import           Basement.Monad
import           Basement.Types.OffsetSize
import qualified Basement.Block         as BLK
import qualified Basement.Block.Mutable as BLK

import qualified Basement.UArray.Mutable as MUV
import qualified Basement.UArray as UV
import qualified Basement.BoxedArray as BA

-- | Collection of things that can be made mutable, modified and then freezed into an MutableFreezed collection
class MutableCollection c where
    -- unfortunately: cannot set mutUnsafeWrite to default to mutWrite .. same for read..
    {-# MINIMAL thaw, freeze, mutNew, mutWrite, mutRead, mutUnsafeWrite, mutUnsafeRead #-}
    type MutableFreezed c
    type MutableKey c
    type MutableValue c

    unsafeThaw   :: PrimMonad prim => MutableFreezed c -> prim (c (PrimState prim))
    unsafeThaw = thaw
    unsafeFreeze :: PrimMonad prim => c (PrimState prim) -> prim (MutableFreezed c)
    unsafeFreeze = freeze

    thaw   :: PrimMonad prim => MutableFreezed c -> prim (c (PrimState prim))
    freeze :: PrimMonad prim => c (PrimState prim) -> prim (MutableFreezed c)

    mutNew :: PrimMonad prim => CountOf (MutableValue c) -> prim (c (PrimState prim))

    mutUnsafeWrite :: PrimMonad prim => c (PrimState prim) -> MutableKey c -> MutableValue c -> prim ()
    mutWrite       :: PrimMonad prim => c (PrimState prim) -> MutableKey c -> MutableValue c -> prim ()
    mutUnsafeRead :: PrimMonad prim => c (PrimState prim) -> MutableKey c -> prim (MutableValue c)
    mutRead       :: PrimMonad prim => c (PrimState prim) -> MutableKey c -> prim (MutableValue c)

instance UV.PrimType ty => MutableCollection (MUV.MUArray ty) where
    type MutableFreezed (MUV.MUArray ty) = UV.UArray ty
    type MutableKey (MUV.MUArray ty) = Offset ty
    type MutableValue (MUV.MUArray ty) = ty

    thaw = UV.thaw
    freeze = UV.freeze
    unsafeThaw = UV.unsafeThaw
    unsafeFreeze = UV.unsafeFreeze

    mutNew = MUV.new

    mutUnsafeWrite = MUV.unsafeWrite
    mutUnsafeRead = MUV.unsafeRead
    mutWrite = MUV.write
    mutRead = MUV.read

instance UV.PrimType ty => MutableCollection (BLK.MutableBlock ty) where
    type MutableFreezed (BLK.MutableBlock ty) = BLK.Block ty
    type MutableKey (BLK.MutableBlock ty) = Offset ty
    type MutableValue (BLK.MutableBlock ty) = ty

    thaw = BLK.thaw
    freeze = BLK.freeze
    unsafeThaw = BLK.unsafeThaw
    unsafeFreeze = BLK.unsafeFreeze

    mutNew = BLK.new

    mutUnsafeWrite = BLK.unsafeWrite
    mutUnsafeRead = BLK.unsafeRead
    mutWrite = BLK.write
    mutRead = BLK.read

instance MutableCollection (BA.MArray ty) where
    type MutableFreezed (BA.MArray ty) = BA.Array ty
    type MutableKey (BA.MArray ty) = Offset ty
    type MutableValue (BA.MArray ty) = ty

    thaw = BA.thaw
    freeze = BA.freeze
    unsafeThaw = BA.unsafeThaw
    unsafeFreeze = BA.unsafeFreeze

    mutNew = BA.new
    mutUnsafeWrite = BA.unsafeWrite
    mutUnsafeRead = BA.unsafeRead
    mutWrite = BA.write
    mutRead = BA.read
