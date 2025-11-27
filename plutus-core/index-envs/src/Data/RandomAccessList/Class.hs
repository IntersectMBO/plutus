{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.RandomAccessList.Class
  ( RandomAccessList (..)
  , Data.RandomAccessList.Class.head
  , Data.RandomAccessList.Class.tail
  , AsRAL (..)
  ) where

import Data.Kind
import Data.List qualified as List
#if MIN_VERSION_base(4,19,0)
-- Avoid a compiler warning about unused package `extra`.
import Data.List.Extra ()
#else
import Data.List.Extra qualified as List
#endif
import Data.Maybe (fromJust, fromMaybe)
import Data.RAList qualified as RAL
import Data.Vector.NonEmpty qualified as NEV
import Data.Word
import GHC.Exts

{-| Typeclass for various types implementing the "signature" of a random-access list.

A true random-access list should have good asymptotic behaviour for these methods also,
but for convenience we also provide implementations for e.g. '[a]', which has bad
lookup performance. -}
class RandomAccessList e where
  -- | The type of elements in the list.
  type Element e :: Type

  -- | The empty list.
  empty :: e

  -- | Prepend an element to the list.
  cons :: Element e -> e -> e

  -- | Un-prepend an element to the list.
  uncons :: e -> Maybe (Element e, e)

  -- | Get the length of the list. May have linear complexity, but useful.
  length :: e -> Word64

  {-# INLINEABLE consSlab #-}

  {-| Prepend many elements to the list. Has a default implementation, but
  implementations can provide more efficient ones. -}
  consSlab :: NEV.NonEmptyVector (Element e) -> e -> e
  consSlab vec e = NEV.foldr cons e vec

  {-# INLINEABLE indexZero #-}

  -- | Lookup an element in the list. 0-based index.
  indexZero :: e -> Word64 -> Maybe (Element e)
  indexZero e i = indexOne e (i + 1)

  {-# INLINEABLE indexOne #-}

  -- | Lookup an element in the list. 1-based index.
  indexOne :: e -> Word64 -> Maybe (Element e)
  indexOne _ 0 = Nothing
  indexOne e i = indexZero e (i - 1)

  {-# INLINEABLE unsafeIndexZero #-}

  -- | Lookup an element in the list, partially.
  unsafeIndexZero :: e -> Word64 -> Element e
  unsafeIndexZero e = fromJust . indexZero e

  {-# INLINEABLE unsafeIndexOne #-}

  -- | Lookup an element in the list, partially.
  unsafeIndexOne :: e -> Word64 -> Element e
  unsafeIndexOne e = fromJust . indexOne e

-- O(1) worst-case
head :: (RandomAccessList e, a ~ Element e) => e -> a
head = fst . fromMaybe (error "empty list") . uncons
{-# INLINEABLE head #-}

-- O(1) worst-case
tail :: RandomAccessList e => e -> e
tail = snd . fromMaybe (error "empty list") . uncons
{-# INLINEABLE tail #-}

instance RandomAccessList [a] where
  type Element [a] = a

  {-# INLINEABLE empty #-}
  empty = []
  {-# INLINEABLE cons #-}
  cons = (:)
  {-# INLINEABLE uncons #-}
  uncons = List.uncons
  {-# INLINEABLE length #-}
  length = fromIntegral . List.length
  {-# INLINEABLE indexZero #-}
  indexZero l w = l List.!? fromIntegral w

instance RandomAccessList (RAL.RAList a) where
  type Element (RAL.RAList a) = a

  {-# INLINEABLE empty #-}
  empty = mempty
  {-# INLINEABLE cons #-}
  cons = RAL.cons
  {-# INLINEABLE uncons #-}
  uncons = RAL.uncons
  {-# INLINEABLE length #-}
  length = fromIntegral . RAL.length
  {-# INLINEABLE indexZero #-}
  indexZero l w = l RAL.!? fromIntegral w

newtype AsRAL a = AsRAL a

instance RandomAccessList e => IsList (AsRAL e) where
  type Item (AsRAL e) = Element e
  fromList l = AsRAL $ foldr cons empty l
  toList (AsRAL e) = List.unfoldr uncons e
