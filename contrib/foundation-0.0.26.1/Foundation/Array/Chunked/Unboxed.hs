-- |
-- Module      : Foundation.Array.Chunked.Unboxed
-- License     : BSD-style -- Maintainer  : Alfredo Di Napoli <alfredo.dinapoli@gmail.com>
-- Stability   : experimental
-- Portability : portable
--
-- Simple array-of-arrays abstraction
--
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Foundation.Array.Chunked.Unboxed
    ( ChunkedUArray
    ) where

import           Data.Typeable
import           Control.Arrow ((***))
import           Basement.BoxedArray (Array)
import qualified Basement.BoxedArray as A
import           Basement.Exception
import           Basement.UArray (UArray)
import qualified Basement.UArray as U
import           Basement.Compat.Bifunctor
import           Basement.Compat.Semigroup
import           Basement.Compat.Base
import           Basement.Types.OffsetSize
import           Basement.PrimType
import           GHC.ST

import           Foundation.Numerical
import           Foundation.Primitive
import qualified Foundation.Collection as C


newtype ChunkedUArray ty = ChunkedUArray (Array (UArray ty))
                      deriving (Show, Ord, Typeable)

instance PrimType ty => Eq (ChunkedUArray ty) where
  (==) = equal
instance NormalForm (ChunkedUArray ty) where
    toNormalForm (ChunkedUArray spine) = toNormalForm spine

instance Semigroup (ChunkedUArray a) where
    (<>) = append
instance Monoid (ChunkedUArray a) where
    mempty  = empty
    mappend = append
    mconcat = concat

type instance C.Element (ChunkedUArray ty) = ty

instance PrimType ty => IsList (ChunkedUArray ty) where
    type Item (ChunkedUArray ty) = ty
    fromList = vFromList
    toList = vToList

instance PrimType ty => C.Foldable (ChunkedUArray ty) where
    foldl' = foldl'
    foldr = foldr
    -- Use the default foldr' instance

instance PrimType ty => C.Collection (ChunkedUArray ty) where
    null = null
    length = length
    elem   = elem
    minimum = minimum
    maximum = maximum
    all p (ChunkedUArray cua) = A.all (U.all p) cua
    any p (ChunkedUArray cua) = A.any (U.any p) cua

instance PrimType ty => C.Sequential (ChunkedUArray ty) where
    take = take
    drop = drop
    splitAt = splitAt
    revTake = revTake
    revDrop = revDrop
    splitOn = splitOn
    break = break
    breakEnd = breakEnd
    intersperse = intersperse
    filter = filter
    reverse = reverse
    unsnoc = unsnoc
    uncons = uncons
    snoc = snoc
    cons = cons
    find = find
    sortBy = sortBy
    singleton = fromList . (:[])
    replicate n = fromList . C.replicate n

instance PrimType ty => C.IndexedCollection (ChunkedUArray ty) where
    (!) l n
        | isOutOfBound n (length l) = Nothing
        | otherwise                     = Just $ index l n
    findIndex predicate c = loop 0
      where
        !len = length c
        loop i
            | i .==# len = Nothing
            | otherwise  =
                if predicate (unsafeIndex c i) then Just i else Nothing

empty :: ChunkedUArray ty
empty = ChunkedUArray A.empty

append :: ChunkedUArray ty -> ChunkedUArray ty -> ChunkedUArray ty
append (ChunkedUArray a1) (ChunkedUArray a2) = ChunkedUArray (mappend a1 a2)

concat :: [ChunkedUArray ty] -> ChunkedUArray ty
concat x = ChunkedUArray (mconcat $ fmap (\(ChunkedUArray spine) -> spine) x)

vFromList :: PrimType ty => [ty] -> ChunkedUArray ty
vFromList l = ChunkedUArray $ A.singleton $ fromList l

vToList :: PrimType ty => ChunkedUArray ty -> [ty]
vToList (ChunkedUArray a) = mconcat $ toList $ toList <$> a

null :: PrimType ty => ChunkedUArray ty -> Bool
null (ChunkedUArray array) =
    C.null array || allNulls 0
  where
    !len = A.length array
    allNulls !idx
      | idx .==# len = True
      | otherwise    = C.null (array `A.unsafeIndex` idx) && allNulls (idx + 1)

-- | Returns the length of this `ChunkedUArray`, by summing each inner length.
-- Complexity: O(n) where `n` is the number of chunks, as U.length u is O(1).
length :: PrimType ty => ChunkedUArray ty -> CountOf ty
length (ChunkedUArray array) = C.foldl' (\acc l -> acc + U.length l) 0 array

-- | Returns `True` if the given element is contained in the `ChunkedUArray`.
-- Complexity: O(n) where `n` is the number of chunks, as U.length u is O(1).
elem :: PrimType ty => ty -> ChunkedUArray ty -> Bool
elem el (ChunkedUArray array) = loop 0
  where
    !len = A.length array
    loop i
        | i .==# len = False
        | otherwise  =
            case C.elem el (A.unsafeIndex array i) of
                True  -> True
                False -> loop (i+1)

-- | Fold a `ChunkedUArray' leftwards strictly. Implemented internally using a double
-- fold on the nested Array structure. Other folds implemented analogously.
foldl' :: PrimType ty => (a -> ty -> a) -> a -> ChunkedUArray ty -> a
foldl' f initialAcc (ChunkedUArray cua) = A.foldl' (U.foldl' f) initialAcc cua

foldr :: PrimType ty => (ty -> a -> a) -> a -> ChunkedUArray ty -> a
foldr f initialAcc (ChunkedUArray cua) = A.foldr (flip $ U.foldr f) initialAcc cua

minimum :: (Ord ty, PrimType ty) => C.NonEmpty (ChunkedUArray ty) -> ty
minimum cua = foldl' min (unsafeIndex cua' 0) (drop 1 cua')
  where
    cua' = C.getNonEmpty cua

maximum :: (Ord ty, PrimType ty) => C.NonEmpty (ChunkedUArray ty) -> ty
maximum cua = foldl' max (unsafeIndex cua' 0) (drop 1 cua')
  where
    cua' = C.getNonEmpty cua

-- | Equality between `ChunkedUArray`.
-- This function is fiddly to write as is not enough to compare for
-- equality the inner `UArray`(s), we need an element-by-element
-- comparison.
equal :: PrimType ty => ChunkedUArray ty -> ChunkedUArray ty -> Bool
equal ca1 ca2 =
    len1 == len2 && go 0
  where
    len1 = length ca1
    len2 = length ca2

    go !x
      | x .==# len1 = True
      | otherwise   = (ca1 `unsafeIndex` x == ca2 `unsafeIndex` x) && go (x + 1)

-- given an offset express in element of ty, return the offset in array in the spine,
-- plus the relative offset in element on this array
findPos :: PrimType ty => Offset ty -> ChunkedUArray ty -> Maybe (Offset (UArray ty), Offset ty)
findPos absOfs (ChunkedUArray array)
    | A.null array = Nothing
    | otherwise    = loop absOfs 0
  where
    !len = A.length array
    loop relOfs outerI
        | outerI .==# len = Nothing -- haven't found what to do
        | relOfs == 0     = Just (outerI, 0)
        | otherwise       =
            let !innera   = A.unsafeIndex array outerI
                !innerLen = U.length innera
             in case removeArraySize relOfs innerLen of
                        Nothing      -> Just (outerI, relOfs)
                        Just relOfs' -> loop relOfs' (outerI + 1)

splitChunk :: Offset (UArray ty) -> ChunkedUArray ty -> (ChunkedUArray ty, ChunkedUArray ty)
splitChunk ofs (ChunkedUArray c) = (ChunkedUArray *** ChunkedUArray) $ A.splitAt (offsetAsSize ofs) c

take :: PrimType ty => CountOf ty -> ChunkedUArray ty -> ChunkedUArray ty
take n c@(ChunkedUArray spine)
    | n <= 0    = empty
    | otherwise =
        case findPos (sizeAsOffset n) c of
            Nothing       -> c
            Just (ofs, 0) -> ChunkedUArray (A.take (offsetAsSize ofs) spine)
            Just (ofs, r) ->
                let uarr = A.unsafeIndex spine ofs
                 in ChunkedUArray (A.take (offsetAsSize ofs) spine `A.snoc` U.take (offsetAsSize r) uarr)

drop :: PrimType ty => CountOf ty -> ChunkedUArray ty -> ChunkedUArray ty
drop n c@(ChunkedUArray spine)
    | n <= 0    = c
    | otherwise =
        case findPos (sizeAsOffset n) c of
            Nothing       -> empty
            Just (ofs, 0) -> ChunkedUArray (A.drop (offsetAsSize ofs) spine)
            Just (ofs, r) ->
                let uarr = A.unsafeIndex spine ofs
                 in ChunkedUArray (U.drop (offsetAsSize r) uarr `A.cons` A.drop (offsetAsSize ofs+1) spine)

splitAt :: PrimType ty => CountOf ty -> ChunkedUArray ty -> (ChunkedUArray ty, ChunkedUArray ty)
splitAt n c@(ChunkedUArray spine)
    | n <= 0    = (empty, c)
    | otherwise =
        case findPos (sizeAsOffset n) c of
            Nothing       -> (c, empty)
            Just (ofs, 0) -> splitChunk ofs c
            Just (ofs, offsetAsSize -> r) ->
                let uarr = A.unsafeIndex spine ofs
                 in ( ChunkedUArray (A.take (offsetAsSize ofs) spine `A.snoc` U.take r uarr)
                    , ChunkedUArray (U.drop r uarr `A.cons` A.drop (offsetAsSize ofs+1) spine)
                    )

revTake :: PrimType ty => CountOf ty -> ChunkedUArray ty -> ChunkedUArray ty
revTake n c = case length c - n of
    Nothing -> c
    Just elems -> drop elems c

revDrop :: PrimType ty => CountOf ty -> ChunkedUArray ty -> ChunkedUArray ty
revDrop n c = case length c - n of
    Nothing -> empty
    Just keepElems -> take keepElems c

-- TODO: Improve implementation.
splitOn :: PrimType ty => (ty -> Bool) -> ChunkedUArray ty -> [ChunkedUArray ty]
splitOn p = fmap fromList . C.splitOn p . toList

-- TODO: Improve implementation.
break :: PrimType ty => (ty -> Bool) -> ChunkedUArray ty -> (ChunkedUArray ty, ChunkedUArray ty)
break p = bimap fromList fromList . C.break p . toList

-- TODO: Improve implementation.
breakEnd :: PrimType ty => (ty -> Bool) -> ChunkedUArray ty -> (ChunkedUArray ty, ChunkedUArray ty)
breakEnd p = bimap fromList fromList . C.breakEnd p . toList

-- TODO: Improve implementation.
intersperse :: PrimType ty => ty -> ChunkedUArray ty -> ChunkedUArray ty
intersperse el = fromList . C.intersperse el . toList

-- TODO: Improve implementation.
reverse :: PrimType ty => ChunkedUArray ty -> ChunkedUArray ty
reverse = fromList . C.reverse . toList

-- TODO: Improve implementation.
filter :: PrimType ty => (ty -> Bool) -> ChunkedUArray ty -> ChunkedUArray ty
filter p = fromList . C.filter p . toList

-- TODO: Improve implementation.
unsnoc :: PrimType ty => ChunkedUArray ty -> Maybe (ChunkedUArray ty, ty)
unsnoc v = first fromList <$> (C.unsnoc $ toList v)

-- TODO: Improve implementation.
uncons :: PrimType ty => ChunkedUArray ty -> Maybe (ty, ChunkedUArray ty)
uncons v = second fromList <$> (C.uncons $ toList v)

cons :: PrimType ty => ty -> ChunkedUArray ty -> ChunkedUArray ty
cons el (ChunkedUArray inner) = ChunkedUArray $ runST $ do
  let newLen = C.length inner + 1
  newArray   <- A.new newLen
  let single = fromList [el]
  A.unsafeWrite newArray 0 single
  A.unsafeCopyAtRO newArray (Offset 1) inner (Offset 0) (C.length inner)
  A.unsafeFreeze newArray

snoc :: PrimType ty => ChunkedUArray ty -> ty -> ChunkedUArray ty
snoc (ChunkedUArray spine) el = ChunkedUArray $ runST $ do
  newArray  <- A.new (A.length spine + 1)
  let single = U.singleton el
  A.unsafeCopyAtRO newArray (Offset 0) spine (Offset 0) (C.length spine)
  A.unsafeWrite newArray (sizeAsOffset $ A.length spine) single
  A.unsafeFreeze newArray

-- TODO optimise
find :: PrimType ty => (ty -> Bool) -> ChunkedUArray ty -> Maybe ty
find fn v = loop 0
  where
    len = length v
    loop !idx
      | idx .==# len = Nothing
      | otherwise    =
        let currentElem = v `unsafeIndex` idx
        in case fn currentElem of
          True  -> Just currentElem
          False -> loop (idx + 1)

-- TODO: Improve implementation.
sortBy :: PrimType ty => (ty -> ty -> Ordering) -> ChunkedUArray ty -> ChunkedUArray ty
sortBy p = fromList . C.sortBy p . toList

index :: PrimType ty => ChunkedUArray ty -> Offset ty -> ty
index array n
    | isOutOfBound n len = outOfBound OOB_Index n len
    | otherwise          = unsafeIndex array n
  where len = length array
{-# INLINE index #-}

unsafeIndex :: PrimType ty => ChunkedUArray ty -> Offset ty -> ty
unsafeIndex (ChunkedUArray array) idx = go (A.unsafeIndex array 0) 0 idx
  where
    go u globalIndex 0 = case C.null u of
      -- Skip empty chunks.
      True  -> go (A.unsafeIndex array (globalIndex + 1)) (globalIndex + 1) 0
      False -> U.unsafeIndex u 0
    go u !globalIndex !i
      -- Skip empty chunks.
      | C.null u  = go (A.unsafeIndex array (globalIndex + 1)) (globalIndex + 1) i
      | otherwise =
          case removeArraySize i (U.length u) of
              Just i' -> go (A.unsafeIndex array (globalIndex + 1)) (globalIndex + 1) i'
              Nothing -> U.unsafeIndex u i

{-# INLINE unsafeIndex #-}

removeArraySize :: Offset ty -> CountOf ty -> Maybe (Offset ty)
removeArraySize (Offset ty) (CountOf s)
    | ty >= s   = Just (Offset (ty - s))
    | otherwise = Nothing
