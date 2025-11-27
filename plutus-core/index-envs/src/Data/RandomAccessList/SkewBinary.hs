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
Bangs in the local definitions of 'contIndexZero' are needed to tell GHC that the functions are
strict in the 'Word64' argument, so that GHC produces workers operating on @Word64#@.

The function itself is CPS-ed, so that the arguments force the local definitions to be retained
within 'contIndexZero' instead of being pulled out via full-laziness or some other optimization
pass. This ensures that when 'contIndexZero' gets inlined, the local definitions appear directly
in the GHC Core, allowing GHC to inline the arguments of 'contIndexZero' and transform the whole
thing into a beautiful recursive join point full of @Word64#@s, i.e. allocating very little if
anything at all.
-}

-- See Note [Optimizations of contIndexZero].
contIndexZero :: forall a b. b -> (a -> b) -> RAList a -> Word64 -> b
contIndexZero z f = findTree
  where
    findTree :: RAList a -> Word64 -> b
    -- See Note [Optimizations of contIndexZero].
    findTree Nil !_ = z
    findTree (BHead w t ts) i =
      if i < w
        then indexTree w i t
        else findTree ts (i - w)

    indexTree :: Word64 -> Word64 -> Tree a -> b
    -- See Note [Optimizations of contIndexZero].
    indexTree !w 0 t = case t of
      Node x _ _ -> f x
      Leaf x -> if w == 1 then f x else z
    indexTree _ _ (Leaf _) = z
    indexTree treeSize offset (Node _ t1 t2) =
      let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
       in if offset <= halfSize
            then indexTree halfSize (offset - 1) t1
            else indexTree halfSize (offset - 1 - halfSize) t2
{-# INLINE contIndexZero #-}

contIndexOne :: forall a b. b -> (a -> b) -> RAList a -> Word64 -> b
contIndexOne z _ _ 0 = z
contIndexOne z f t n = contIndexZero z f t (n - 1)
{-# INLINE contIndexOne #-}

-- 0-based
unsafeIndexZero :: RAList a -> Word64 -> a
unsafeIndexZero = contIndexZero (error "out of bounds") id
{-# INLINE unsafeIndexZero #-}

-- 0-based
safeIndexZero :: RAList a -> Word64 -> Maybe a
safeIndexZero = contIndexZero Nothing Just
{-# INLINE safeIndexZero #-}

-- 1-based
unsafeIndexOne :: RAList a -> Word64 -> a
unsafeIndexOne = contIndexOne (error "out of bounds") id
{-# INLINE unsafeIndexOne #-}

-- 1-based
safeIndexOne :: RAList a -> Word64 -> Maybe a
safeIndexOne = contIndexOne Nothing Just
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
