{-# LANGUAGE TypeFamilies #-}
module Data.DeBruijnEnv
    ( DeBruijnEnv (..)
    , BRAL.RAList (..)
    , RelativizedMap (..)
    ) where

import Data.IntMap.Strict qualified as IM
import Data.Kind
import Data.Maybe (fromJust)
import Data.RAList qualified as RAL
import Data.RandomAccessList.SkewBinary qualified as BRAL
import Data.Word

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
    -- | Lookup an element in the environment. Assumed to be **1-indexed**.
    index :: e -> Word64 -> Maybe (Element e)
    {-# INLINABLE unsafeIndex #-}
    -- | Lookup an element in the environment, partially.
    unsafeIndex :: e -> Word64 -> Element e
    unsafeIndex e = fromJust . index e

instance DeBruijnEnv (BRAL.RAList a) where
    type Element (BRAL.RAList a) = a

    {-# INLINABLE empty #-}
    empty = BRAL.Nil
    {-# INLINABLE cons #-}
    cons = BRAL.Cons
    {-# INLINABLE index #-}
    index = BRAL.safeIndexOne
    {-# INLINABLE unsafeIndex #-}
    unsafeIndex = BRAL.unsafeIndexOne

-- | A sequence implemented by a map from "levels" to values and a counter giving the "current" level.
data RelativizedMap a = RelativizedMap (IM.IntMap a) {-# UNPACK #-} !Word64
    deriving stock Show

instance DeBruijnEnv (RelativizedMap a) where
    type Element (RelativizedMap a) = a

    {-# INLINABLE empty #-}
    empty = RelativizedMap mempty 0
    {-# INLINABLE cons #-}
    cons a (RelativizedMap im l) = RelativizedMap (IM.insert (fromIntegral l) a im) (l+1)
    {-# INLINABLE index #-}
    index (RelativizedMap im l) w = IM.lookup (fromIntegral l - fromIntegral w) im

instance DeBruijnEnv (RAL.RAList  a) where
    type Element (RAL.RAList a) = a

    {-# INLINABLE empty #-}
    empty = mempty
    {-# INLINABLE cons #-}
    cons = RAL.cons
    {-# INLINABLE index #-}
    -- RAL is 0-indexed
    index l w = l RAL.!? fromIntegral (w-1)
