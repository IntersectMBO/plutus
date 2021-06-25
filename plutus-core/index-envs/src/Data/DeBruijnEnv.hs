{-# LANGUAGE TypeFamilies #-}
module Data.DeBruijnEnv (DeBruijnEnv (..), RelativizedMap (..)) where

import qualified Data.IntMap.Strict               as IM
import           Data.Kind
import           Data.Maybe                       (fromJust)
import qualified Data.RAList                      as RAL
import qualified Data.RandomAccessList.SkewBinary as BRAL

{-|
A class for types that can be used to implement a de Bruijn index environment.
-}
class DeBruijnEnv e where
    -- | The type of elements in the environment.
    type Element e :: Type

    -- | The empty environment.
    empty :: e
    -- | Prepend an element to the environment.
    cons :: Element e -> e -> e
    -- | Lookup an element in the environment.
    index :: e -> Word -> Maybe (Element e)
    {-# INLINABLE unsafeIndex #-}
    -- | Lookup an element in the environment, partially.
    unsafeIndex :: e -> Word -> Element e
    unsafeIndex e i = fromJust $ index e i

instance DeBruijnEnv (BRAL.RAList a) where
    type Element (BRAL.RAList a) = a

    {-# INLINABLE empty #-}
    empty = BRAL.Nil
    {-# INLINABLE cons #-}
    cons = BRAL.Cons
    {-# INLINABLE index #-}
    index = BRAL.safeIndex
    {-# INLINABLE unsafeIndex #-}
    unsafeIndex = BRAL.index

-- | A sequence implemented by a map from "levels" to values and a counter giving the "current" level.
data RelativizedMap a = RelativizedMap (IM.IntMap a) {-# UNPACK #-} !Int

instance DeBruijnEnv (RelativizedMap a) where
    type Element (RelativizedMap a) = a

    {-# INLINABLE empty #-}
    empty = RelativizedMap mempty 0
    {-# INLINABLE cons #-}
    cons a (RelativizedMap im l) = RelativizedMap (IM.insert l a im) (l+1)
    {-# INLINABLE index #-}
    index (RelativizedMap im l) w = IM.lookup (l - fromIntegral w) im

instance DeBruijnEnv (RAL.RAList  a) where
    type Element (RAL.RAList a) = a

    {-# INLINABLE empty #-}
    empty = mempty
    {-# INLINABLE cons #-}
    cons = RAL.cons
    {-# INLINABLE index #-}
    index l w = l RAL.!? fromIntegral w
