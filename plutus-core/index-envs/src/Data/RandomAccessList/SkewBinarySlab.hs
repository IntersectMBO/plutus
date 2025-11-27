{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Data.RandomAccessList.SkewBinarySlab
  ( RAList (Cons, Nil)
  , safeIndexZero
  , unsafeIndexZero
  , Data.RandomAccessList.SkewBinarySlab.null
  , uncons
  , consSlab
  ) where

import Data.Bits (unsafeShiftR)
import Data.Vector.NonEmpty qualified as NEV
import Data.Word
import GHC.Exts (IsList, toList)

import Data.RandomAccessList.Class qualified as RAL

{- Note [Skew binary slab lists]
This module implements a very similar structure to the one in 'SkewBinary', but
instead of storing a single value at each node, it instead stores potentially many
values.

The advantage of this is that we can rapidly cons on a collection of values, and that
if we do this regularly then the size of the structure will grow more slowly than
the number of values stored, giving us a discount on our lookup performance (which
depends on the size of the structure!).

The disadvantages are several:
- It's more complex.
- We need another intermediary type, which means more indirect lookups.
- We need to store another size in the spine of the list *and* in the tree nodes,
since a) the structure size no longer tells us the element count, and b) as we
traverse a tree it's no longer true that the size on each side is always half of
the overall size.

Benchmarking suggests that it *is* slightly slower than the normal version
on the non-slab-based workflows, but it's much faster on the slab-based workflows.

So it's not an unqualified win, but it may be better in some cases.
-}

-- Why not just store `NonEmptyVector`s and add singleton values by making singleton
-- vectors? The answer is that using only vectors makes simple consing significantly
-- slower, and doesn't obviously make the other code paths faster.
{-| The values that can be stored in a node. Either a single value, or a non-empty vector of
values. -}
data Values a = One a | Many {-# UNPACK #-} !(NEV.NonEmptyVector a)
  deriving stock (Eq, Show)

valuesCount :: Values a -> Word64
valuesCount (One _) = 1
valuesCount (Many v) = fromIntegral $ NEV.length v

unsafeIndexValues :: Word64 -> Values a -> a
unsafeIndexValues 0 (One a) = a
unsafeIndexValues _ (One _) = error "out of bounds"
unsafeIndexValues i (Many v) = v NEV.! fromIntegral i

safeIndexValues :: Word64 -> Values a -> Maybe a
safeIndexValues 0 (One a) = Just a
safeIndexValues _ (One _) = Nothing
safeIndexValues i (Many v) = v NEV.!? fromIntegral i

-- O(1)
unconsValues :: Values a -> RAList a -> (a, RAList a)
unconsValues (One x) l = (x, l)
unconsValues (Many v) l =
  -- unconsing vectors is actually O(1), which is important!
  let (x, xs) = NEV.uncons v
      remaining = case NEV.fromVector xs of
        Just v' -> consSlab v' l
        Nothing -> l
   in (x, remaining)

-- | A complete binary tree.
data Tree a
  = Leaf !(Values a)
  | -- Nodes track the number of elements in the tree (including those in the node)
    Node {-# UNPACK #-} !Word64 !(Values a) !(Tree a) !(Tree a)
  deriving stock (Eq, Show)

treeCount :: Tree a -> Word64
treeCount (Leaf v) = valuesCount v
treeCount (Node s _ _ _) = s

unsafeIndexTree :: Word64 -> Tree a -> a
unsafeIndexTree offset (Leaf v) = unsafeIndexValues offset v
unsafeIndexTree offset (Node _ v t1 t2) =
  let nCount = valuesCount v
   in if offset < nCount
        then unsafeIndexValues offset v
        else
          let offset' = offset - nCount
              lCount = treeCount t1
           in if offset' < lCount
                then unsafeIndexTree offset' t1
                else unsafeIndexTree (offset' - lCount) t2

safeIndexTree :: Word64 -> Tree a -> Maybe a
safeIndexTree offset (Leaf v) = safeIndexValues offset v
safeIndexTree offset (Node _ v t1 t2) =
  let nCount = valuesCount v
   in if offset < nCount
        then safeIndexValues offset v
        else
          let offset' = offset - nCount
              lCount = treeCount t1
           in if offset' < lCount
                then safeIndexTree offset' t1
                else safeIndexTree (offset' - lCount) t2

{-| A strict list of complete binary trees accompanied by their node size.
The trees appear in >=-node size order.
Note: this list is strict in its spine, unlike the Prelude list -}
data RAList a
  = BHead
      {-# UNPACK #-} !Word64
      -- ^ the number of nodes in the head tree
      !(Tree a)
      -- ^ the head tree
      !(RAList a)
      -- ^ the tail trees
  | Nil
  deriving stock (Show)
  deriving (IsList) via RAL.AsRAL (RAList a)

-- Can't use the derived instance because it's no longer the case that lists with
-- the same contents have to have the same structure! Could definitely write a
-- faster implementation if it matters, though.
instance Eq a => Eq (RAList a) where
  l == l' = toList l == toList l'

null :: RAList a -> Bool
null Nil = True
null _ = False
{-# INLINEABLE null #-}

{-# COMPLETE Cons, Nil #-}
{-# COMPLETE BHead, Nil #-}

-- /O(1)/
pattern Cons :: a -> RAList a -> RAList a
pattern Cons x xs <- (uncons -> Just (x, xs))
  where
    Cons x xs = cons x xs

-- O(1) worst-case
consValues :: Values a -> RAList a -> RAList a
consValues x l = case l of
  (BHead w1 t1 (BHead w2 t2 ts'))
    | w1 == w2 ->
        let ts = w1 + w2 + 1
            ec = treeCount t1 + treeCount t2 + valuesCount x
         in BHead ts (Node ec x t1 t2) ts'
  ts -> BHead 1 (Leaf x) ts

-- O(1) worst-case
cons :: a -> RAList a -> RAList a
cons x = consValues (One x)
{-# INLINE cons #-}

-- O(1) worst-case
consSlab :: NEV.NonEmptyVector a -> RAList a -> RAList a
consSlab x = consValues (Many x)
{-# INLINE consSlab #-}

-- /O(1)/
-- 'uncons' is a bit funny: if we uncons a vector of values
-- initially, we will then uncons the front of *that* and possibly
-- cons the rest back on! Fortunately all these operations are O(1),
-- so it adds up to being okay.
uncons :: RAList a -> Maybe (a, RAList a)
uncons = \case
  BHead _ (Leaf v) ts -> Just $ unconsValues v ts
  BHead _ (Node treeSize x t1 t2) ts ->
    -- probably faster than `div w 2`
    let halfSize = unsafeShiftR treeSize 1
     in -- split the node in two)
        Just $ unconsValues x (BHead halfSize t1 $ BHead halfSize t2 ts)
  Nil -> Nothing

-- 0-based
unsafeIndexZero :: RAList a -> Word64 -> a
unsafeIndexZero Nil _ = error "out of bounds"
unsafeIndexZero (BHead _ t ts) !i =
  let tCount = treeCount t
   in if i < tCount
        then unsafeIndexTree i t
        else unsafeIndexZero ts (i - tCount)

-- 0-based
safeIndexZero :: RAList a -> Word64 -> Maybe a
safeIndexZero Nil _ = Nothing
safeIndexZero (BHead _ t ts) !i =
  let tCount = treeCount t
   in if i < tCount
        then safeIndexTree i t
        else safeIndexZero ts (i - tCount)

instance RAL.RandomAccessList (RAList a) where
  type Element (RAList a) = a

  {-# INLINEABLE empty #-}
  empty = Nil
  {-# INLINEABLE cons #-}
  cons = Cons
  {-# INLINEABLE uncons #-}
  uncons = uncons
  {-# INLINEABLE length #-}
  length Nil = 0
  length (BHead _ t tl) = treeCount t + RAL.length tl
  {-# INLINEABLE consSlab #-}
  consSlab = consSlab
  {-# INLINEABLE indexZero #-}
  indexZero l i = safeIndexZero l i
  {-# INLINEABLE unsafeIndexZero #-}
  unsafeIndexZero l i = unsafeIndexZero l i
