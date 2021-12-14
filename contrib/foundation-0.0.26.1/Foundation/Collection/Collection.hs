-- |
-- Module      : Foundation.Collection.Collection
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : portable
--
-- Provide basic collection information. It's difficult to provide a
-- unified interface to all sorts of collection, but when creating this
-- API we had the following types in mind:
--
-- * List (e.g [a])
-- * Array
-- * Collection of collection (e.g. deque)
-- * Hashtables, Trees
--
-- an API to rules them all, and in the darkness bind them.
--
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foundation.Collection.Collection
    ( Collection(..)
    -- * NonEmpty Property
    , NonEmpty
    , getNonEmpty
    , nonEmpty
    , nonEmpty_
    , nonEmptyFmap
    , and
    , or
    ) where

import           Basement.Compat.Base hiding (and)
import           Basement.Types.OffsetSize
import           Basement.Types.AsciiString
import           Basement.Exception (NonEmptyCollectionIsEmpty(..))
import           Foundation.Collection.Element
import           Basement.NonEmpty
import qualified Data.List
import qualified Basement.Block as BLK
import qualified Basement.UArray as UV
import qualified Basement.BoxedArray as BA
import qualified Basement.String as S

-- | Smart constructor to create a NonEmpty collection
--
-- If the collection is empty, then Nothing is returned
-- Otherwise, the collection is wrapped in the NonEmpty property
nonEmpty :: Collection c => c -> Maybe (NonEmpty c)
nonEmpty c
    | null c    = Nothing
    | otherwise = Just (NonEmpty c)

-- | same as 'nonEmpty', but assume that the collection is non empty,
-- and return an asynchronous error if it is.
nonEmpty_ :: Collection c => c -> NonEmpty c
nonEmpty_ c
    | null c    = throw NonEmptyCollectionIsEmpty
    | otherwise = NonEmpty c

nonEmptyFmap :: Functor f => (a -> b) -> NonEmpty (f a) -> NonEmpty (f b)
nonEmptyFmap f (NonEmpty l) = NonEmpty (fmap f l)

-- | A set of methods for ordered colection
class (IsList c, Item c ~ Element c) => Collection c where
    {-# MINIMAL null, length, (elem | notElem), minimum, maximum, all, any #-}
    -- | Check if a collection is empty
    null :: c -> Bool

    -- | Length of a collection (number of Element c)
    length :: c -> CountOf (Element c)

    -- | Check if a collection contains a specific element
    --
    -- This is the inverse of `notElem`.
    elem :: forall a . (Eq a, a ~ Element c) => Element c -> c -> Bool
    elem e col = not $ e `notElem` col
    -- | Check if a collection does *not* contain a specific element
    --
    -- This is the inverse of `elem`.
    notElem :: forall a . (Eq a, a ~ Element c) => Element c -> c -> Bool
    notElem e col = not $ e `elem` col

    -- | Get the maximum element of a collection
    maximum :: forall a . (Ord a, a ~ Element c) => NonEmpty c -> Element c
    -- | Get the minimum element of a collection
    minimum :: forall a . (Ord a, a ~ Element c) => NonEmpty c -> Element c

    -- | Determine is any elements of the collection satisfy the predicate
    any :: (Element c -> Bool) -> c -> Bool

    -- | Determine is all elements of the collection satisfy the predicate
    all :: (Element c -> Bool) -> c -> Bool

instance Collection [a] where
    null = Data.List.null
    length = CountOf . Data.List.length

    elem = Data.List.elem
    notElem = Data.List.notElem

    minimum = Data.List.minimum . getNonEmpty
    maximum = Data.List.maximum . getNonEmpty

    any = Data.List.any
    all = Data.List.all

instance UV.PrimType ty => Collection (BLK.Block ty) where
    null = (==) 0 . BLK.length
    length = BLK.length
    elem = BLK.elem
    minimum = BLK.foldl1' min
    maximum = BLK.foldl1' max
    all = BLK.all
    any = BLK.any

instance UV.PrimType ty => Collection (UV.UArray ty) where
    null    = UV.null
    length  = UV.length
    elem    = UV.elem
    minimum = UV.foldl1' min
    maximum = UV.foldl1' max
    all     = UV.all
    any     = UV.any


instance Collection (BA.Array ty) where
    null    = BA.null
    length  = BA.length
    elem    = BA.elem
    minimum = BA.foldl1' min
    maximum = BA.foldl1' max
    all     = BA.all
    any     = BA.any

deriving instance Collection AsciiString

instance Collection S.String where
    null = S.null
    length = S.length
    elem = S.elem
    minimum = Data.List.minimum . toList . getNonEmpty -- TODO faster implementation
    maximum = Data.List.maximum . toList . getNonEmpty -- TODO faster implementation
    all = S.all
    any = S.any

instance Collection c => Collection (NonEmpty c) where
    null _ = False
    length = length . getNonEmpty
    elem e = elem e . getNonEmpty
    maximum = maximum . getNonEmpty
    minimum = minimum . getNonEmpty
    all p = all p . getNonEmpty
    any p = any p . getNonEmpty

-- | Return True if all the elements in the collection are True
and :: (Collection col, Element col ~ Bool) => col -> Bool
and = all (== True)

-- | Return True if at least one element in the collection is True
or :: (Collection col, Element col ~ Bool) => col -> Bool
or = any (== True)
