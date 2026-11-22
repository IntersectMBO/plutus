{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Data.RandomAccessList.SkewBinary
  ( RAList (Cons, Nil)
  , contIndexZero
  , contIndexOne
  , safeIndexZero
  , unsafeIndexZero
  , safeIndexOne
  , unsafeIndexOne
  , Data.RandomAccessList.SkewBinary.null
  , uncons
  ) where

import Data.Bits (setBit, unsafeShiftL, unsafeShiftR)
import Data.Word
import GHC.Exts

import Data.RandomAccessList.Class qualified as RAL

-- 'Node' appears first to make it more likely for GHC to reorder pattern matches to make the 'Node'
-- one appear first (which makes it more efficient).
{-| A complete binary tree.
Note: the size of the tree is not stored/cached,
unless it appears as a root tree in 'RAList', which the size is stored inside the Cons. -}
data Tree a
  = Node a !(Tree a) !(Tree a)
  | Leaf a
  deriving stock (Eq, Show)

{-| A strict list of complete binary trees accompanied by their size.
The trees appear in >=-size order.
Note: this list is strict in its spine, unlike the Prelude list -}
data RAList a
  = BHead
      {-# UNPACK #-} !Word64
      -- ^ the size of the head tree
      !(Tree a)
      -- ^ the head tree
      !(RAList a)
      -- ^ the tail trees
  | Nil
  -- the derived Eq instance is correct,
  -- because binary skew numbers have unique representation
  -- and hence all trees of the same size will have the same structure
  deriving stock (Eq, Show)
  deriving (IsList) via RAL.AsRAL (RAList a)

null :: RAList a -> Bool
null Nil = True
null _ = False
{-# INLINE null #-}

{-# COMPLETE Cons, Nil #-}
{-# COMPLETE BHead, Nil #-}

-- /O(1)/
pattern Cons :: a -> RAList a -> RAList a
pattern Cons x xs <- (uncons -> Just (x, xs))
  where
    Cons x xs = cons x xs

-- O(1) worst-case
cons :: a -> RAList a -> RAList a
cons x = \case
  (BHead w1 t1 (BHead w2 t2 ts'))
    | w1 == w2 ->
        -- 'unsafeShiftL w1 1 `setBit`0' is supposed to be a faster version of '(2*w1)+1'
        BHead (unsafeShiftL w1 1 `setBit` 0) (Node x t1 t2) ts'
  ts -> BHead 1 (Leaf x) ts
{-# INLINE cons #-}

-- /O(1)/
uncons :: RAList a -> Maybe (a, RAList a)
uncons = \case
  BHead _ (Leaf x) ts -> Just (x, ts)
  BHead treeSize (Node x t1 t2) ts ->
    -- probably faster than `div w 2`
    let halfSize = unsafeShiftR treeSize 1
     in -- split the node in two)
        Just (x, BHead halfSize t1 $ BHead halfSize t2 ts)
  Nil -> Nothing
{-# INLINE uncons #-}

{- Note [Optimizations of contIndexZero]
The lookup passes its result to a continuation: 'Nothing' when the index is out of bounds,
or 'Just' the element when it is found. Callers construct their failure result in the
'Nothing' branch. Passing a failure result as a separate argument previously let GHC
allocate the CEK error and its cause before the lookup, even when the lookup succeeded.

The local search functions use the continuation, which keeps them inside 'contIndexZero'
until it is inlined at the call site. GHC can then inline the continuation into the search
and turn the recursive calls into local jumps (join points). When the continuation matches
on the 'Maybe', the 'Just' and 'Nothing' constructors are eliminated along with that match;
the intermediate 'Maybe' does not need to be allocated.

The bangs on the index and tree size tell GHC that the search is strict in these arguments.
This lets it use unboxed 'Word64' values throughout the traversal.
-}

{-| Look up a zero-based index and pass the result to the continuation.
An out-of-bounds index gives 'Nothing'. -}
contIndexZero :: forall a b. (Maybe a -> b) -> RAList a -> Word64 -> b
contIndexZero k = findTree
  where
    findTree :: RAList a -> Word64 -> b
    -- See Note [Optimizations of contIndexZero].
    findTree Nil !_ = k Nothing
    findTree (BHead w t ts) i =
      if i < w
        then indexTree w i t
        else findTree ts (i - w)

    indexTree :: Word64 -> Word64 -> Tree a -> b
    -- See Note [Optimizations of contIndexZero].
    indexTree !w 0 t = case t of
      Node x _ _ -> k (Just x)
      Leaf x -> if w == 1 then k (Just x) else k Nothing
    indexTree _ _ (Leaf _) = k Nothing
    indexTree treeSize offset (Node _ t1 t2) =
      let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
       in if offset <= halfSize
            then indexTree halfSize (offset - 1) t1
            else indexTree halfSize (offset - 1 - halfSize) t2
{-# INLINE contIndexZero #-}

{-| Look up a one-based index and pass the result to the continuation.
Zero and indices beyond the end give 'Nothing'. -}
contIndexOne :: forall a b. (Maybe a -> b) -> RAList a -> Word64 -> b
contIndexOne k _ 0 = k Nothing
contIndexOne k t n = contIndexZero k t (n - 1)
{-# INLINE contIndexOne #-}

-- 0-based
unsafeIndexZero :: RAList a -> Word64 -> a
unsafeIndexZero = contIndexZero $ \case
  Nothing -> error "out of bounds"
  Just x -> x
{-# INLINE unsafeIndexZero #-}

-- 0-based
safeIndexZero :: RAList a -> Word64 -> Maybe a
safeIndexZero = contIndexZero id
{-# INLINE safeIndexZero #-}

-- 1-based
unsafeIndexOne :: RAList a -> Word64 -> a
unsafeIndexOne = contIndexOne $ \case
  Nothing -> error "out of bounds"
  Just x -> x
{-# INLINE unsafeIndexOne #-}

-- 1-based
safeIndexOne :: RAList a -> Word64 -> Maybe a
safeIndexOne = contIndexOne id
{-# INLINE safeIndexOne #-}

instance RAL.RandomAccessList (RAList a) where
  type Element (RAList a) = a

  empty = Nil
  {-# INLINE empty #-}

  cons = Cons
  {-# INLINE cons #-}

  uncons = uncons
  {-# INLINE uncons #-}

  length = go 0
    where
      go !acc Nil = acc
      go !acc (BHead sz _ tl) = go (acc + sz) tl
  {-# INLINE length #-}

  indexZero = safeIndexZero
  {-# INLINE indexZero #-}

  indexOne = safeIndexOne
  {-# INLINE indexOne #-}

  unsafeIndexZero = unsafeIndexZero
  {-# INLINE unsafeIndexZero #-}

  unsafeIndexOne = unsafeIndexOne
  {-# INLINE unsafeIndexOne #-}
