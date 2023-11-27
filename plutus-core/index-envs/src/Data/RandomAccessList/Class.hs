{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
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

-- | Typeclass for various types implementing the "signature" of a random-access list.
--
-- A true random-access list should have good asymptotic behaviour for these methods also,
-- but for convenience we also provide implementations for e.g. '[a]', which has bad
-- lookup performance.
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

    {-# INLINABLE consSlab #-}
    -- | Prepend many elements to the list. Has a default implementation, but
    -- implementations can provide more efficient ones.
    consSlab :: NEV.NonEmptyVector (Element e) -> e -> e
    consSlab vec e = NEV.foldr cons e vec

    {-# INLINABLE indexZero #-}
    -- | Lookup an element in the list. 0-based index.
    indexZero :: e -> Word64 -> Maybe (Element e)
    indexZero e i = indexOne e (i+1)

    {-# INLINABLE indexOne #-}
    -- | Lookup an element in the list. 1-based index.
    indexOne :: e -> Word64 -> Maybe (Element e)
    indexOne _ 0 = Nothing
    indexOne e i = indexZero e (i-1)

    {-# INLINABLE unsafeIndexZero #-}
    -- | Lookup an element in the list, partially.
    unsafeIndexZero :: e -> Word64 -> Element e
    unsafeIndexZero e = fromJust . indexZero e

    {-# INLINABLE unsafeIndexOne #-}
    -- | Lookup an element in the list, partially.
    unsafeIndexOne :: e -> Word64 -> Element e
    unsafeIndexOne e = fromJust . indexOne e

{-# INLINABLE head #-}
-- O(1) worst-case
head :: (RandomAccessList e, a ~ Element e) => e -> a
head = fst . fromMaybe (error "empty list") . uncons

{-# INLINABLE tail #-}
-- O(1) worst-case
tail :: (RandomAccessList e) => e -> e
tail = snd . fromMaybe (error "empty list") . uncons

instance RandomAccessList [a] where
    type Element [a] = a

    {-# INLINABLE empty #-}
    empty = []
    {-# INLINABLE cons #-}
    cons = (:)
    {-# INLINABLE uncons #-}
    uncons = List.uncons
    {-# INLINABLE length #-}
    length = fromIntegral . List.length
    {-# INLINABLE indexZero #-}
    indexZero l w = l List.!? fromIntegral w

instance RandomAccessList (RAL.RAList  a) where
    type Element (RAL.RAList a) = a

    {-# INLINABLE empty #-}
    empty = mempty
    {-# INLINABLE cons #-}
    cons = RAL.cons
    {-# INLINABLE uncons #-}
    uncons = RAL.uncons
    {-# INLINABLE length #-}
    length = fromIntegral . RAL.length
    {-# INLINABLE indexZero #-}
    indexZero l w = l RAL.!? fromIntegral w

newtype AsRAL a = AsRAL a

instance RandomAccessList e => IsList (AsRAL e) where
    type Item (AsRAL e) = Element e
    fromList l = AsRAL $ foldr cons empty l
    toList (AsRAL e) = List.unfoldr uncons e
