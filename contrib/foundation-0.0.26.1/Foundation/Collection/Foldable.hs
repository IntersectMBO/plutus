-- |
-- Module      : Basement.Foldable
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- A mono-morphic re-thinking of the Foldable class
--

{-# LANGUAGE CPP                   #-}

#if MIN_VERSION_base(4,9,0)
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
#endif

module Foundation.Collection.Foldable
    ( Foldable(..)
    , Fold1able(..)
    ) where

import           Basement.Compat.Base
import           Foundation.Collection.Element
import           Basement.NonEmpty
import           Basement.Nat
import qualified Data.List
import qualified Basement.UArray as UV
import qualified Basement.Block as BLK
import qualified Basement.BoxedArray as BA

#if MIN_VERSION_base(4,9,0)
import qualified Basement.Sized.List as LN
import qualified Basement.Sized.Block as BLKN
#endif

-- | Give the ability to fold a collection on itself
class Foldable collection where
    -- | Left-associative fold of a structure.
    --
    -- In the case of lists, foldl, when applied to a binary operator, a starting value (typically the left-identity of the operator), and a list, reduces the list using the binary operator, from left to right:
    --
    -- > foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
    -- Note that to produce the outermost application of the operator the entire input list must be traversed. This means that foldl' will diverge if given an infinite list.
    --
    -- Note that Foundation only provides `foldl'`, a strict version of `foldl` because
    -- the lazy version is seldom useful.

    -- | Left-associative fold of a structure with strict application of the operator.
    foldl' :: (a -> Element collection -> a) -> a -> collection -> a

    -- | Right-associative fold of a structure.
    --
    -- > foldr f z [x1, x2, ..., xn] == x1 `f` (x2 `f` ... (xn `f` z)...)
    foldr :: (Element collection -> a -> a) -> a -> collection -> a

    -- | Right-associative fold of a structure, but with strict application of the operator.
    foldr' :: (Element collection -> a -> a) -> a -> collection -> a
    foldr' f z0 xs = foldl' f' id xs z0 where f' k x z = k $! f x z

-- | Fold1's. Like folds, but they assume to operate on a NonEmpty collection.
class Foldable f => Fold1able f where
    -- | Left associative strict fold.
    foldl1' :: (Element f -> Element f -> Element f) -> NonEmpty f -> Element f
    -- | Right associative lazy fold.
    foldr1  :: (Element f -> Element f -> Element f) -> NonEmpty f -> Element f
    -- | Right associative strict fold.
    --foldr1' :: (Element f -> Element f -> Element f) -> NonEmpty f -> Element f
    --foldr1' f xs = foldl f' id . getNonEmpty
    --  where f' k x z = k $! f x z


----------------------------
-- Foldable instances
----------------------------

instance Foldable [a] where
    foldr = Data.List.foldr
    foldl' = Data.List.foldl'

instance UV.PrimType ty => Foldable (UV.UArray ty) where
    foldr = UV.foldr
    foldl' = UV.foldl'
instance Foldable (BA.Array ty) where
    foldr = BA.foldr
    foldl' = BA.foldl'
instance UV.PrimType ty => Foldable (BLK.Block ty) where
    foldr = BLK.foldr
    foldl' = BLK.foldl'

#if MIN_VERSION_base(4,9,0)
instance Foldable (LN.ListN n a) where
    foldr = LN.foldr
    foldl' = LN.foldl'
instance UV.PrimType ty => Foldable (BLKN.BlockN n ty) where
    foldr = BLKN.foldr
    foldl' = BLKN.foldl'
#endif

----------------------------
-- Fold1able instances
----------------------------

instance Fold1able [a] where
    foldr1  f = Data.List.foldr1  f . getNonEmpty
    foldl1' f = Data.List.foldl1' f . getNonEmpty

instance UV.PrimType ty => Fold1able (UV.UArray ty) where
    foldr1 = UV.foldr1
    foldl1' = UV.foldl1'
instance Fold1able (BA.Array ty) where
    foldr1  = BA.foldr1
    foldl1' = BA.foldl1'
instance UV.PrimType ty => Fold1able (BLK.Block ty) where
    foldr1  = BLK.foldr1
    foldl1' = BLK.foldl1'

#if MIN_VERSION_base(4,9,0)
instance (1 <= n) => Fold1able (LN.ListN n a) where
    foldr1  f = LN.foldr1  f . getNonEmpty
    foldl1' f = LN.foldl1' f . getNonEmpty
#endif
