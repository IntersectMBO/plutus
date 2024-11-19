{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
module Data.RandomAccessList.SkewBinary
    ( RAList(Cons,Nil)
    , safeIndexZero
    , unsafeIndexZero
    , safeIndexOne
    , safeIndexOneCont
    , unsafeIndexOne
    , Data.RandomAccessList.SkewBinary.null
    , uncons
    ) where

import Data.Bits (unsafeShiftR)
import Data.Word
import GHC.Exts

import Data.RandomAccessList.Class qualified as RAL

-- 'Node' appears first to make it more likely for GHC to reorder pattern matches to make the 'Node'
-- one appear first (which makes it more efficient).
-- | A complete binary tree.
-- Note: the size of the tree is not stored/cached,
-- unless it appears as a root tree in 'RAList', which the size is stored inside the Cons.
data Tree a = Node a !(Tree a) !(Tree a)
            | Leaf a
            deriving stock (Eq, Show)

-- | A strict list of complete binary trees accompanied by their size.
-- The trees appear in >=-size order.
-- Note: this list is strict in its spine, unlike the Prelude list
data RAList a = BHead
               {-# UNPACK #-} !Word64 -- ^ the size of the head tree
               !(Tree a) -- ^ the head tree
               !(RAList a) -- ^ the tail trees
             | Nil
             -- the derived Eq instance is correct,
             -- because binary skew numbers have unique representation
             -- and hence all trees of the same size will have the same structure
             deriving stock (Eq, Show)
             deriving (IsList) via RAL.AsRAL (RAList a)

{-# INLINABLE null #-}
null :: RAList a -> Bool
null Nil = True
null _   = False

{-# complete Cons, Nil #-}
{-# complete BHead, Nil #-}

-- /O(1)/
pattern Cons :: a -> RAList a -> RAList a
pattern Cons x xs <- (uncons -> Just (x, xs)) where
  Cons x xs = cons x xs

-- O(1) worst-case
cons :: a -> RAList a -> RAList a
cons x = \case
    (BHead w1 t1 (BHead w2 t2 ts')) | w1 == w2 -> BHead (2*w1+1) (Node x t1 t2) ts'
    ts                                         -> BHead 1 (Leaf x) ts

-- /O(1)/
uncons :: RAList a -> Maybe (a, RAList a)
uncons = \case
    BHead _ (Leaf x) ts -> Just (x, ts)
    BHead treeSize (Node x t1 t2) ts ->
        -- probably faster than `div w 2`
        let halfSize = unsafeShiftR treeSize 1
            -- split the node in two)
        in Just (x, BHead halfSize t1 $ BHead halfSize t2 ts)
    Nil -> Nothing

-- 0-based
unsafeIndexZero :: RAList a -> Word64 -> a
unsafeIndexZero Nil _  = error "out of bounds"
unsafeIndexZero (BHead w t ts) !i  =
    if i < w
    then indexTree w i t
    else unsafeIndexZero ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree a -> a
    indexTree 1 0 (Leaf x) = x
    indexTree _ _ (Leaf _) = error "out of bounds"
    indexTree _ 0 (Node x _ _) = x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
        in if offset <= halfSize
           then indexTree halfSize (offset - 1) t1
           else indexTree halfSize (offset - 1 - halfSize) t2

-- 0-based
safeIndexZero :: RAList a -> Word64 -> Maybe a
safeIndexZero Nil _  = Nothing
safeIndexZero (BHead w t ts) !i  =
    if i < w
    then indexTree w i t
    else safeIndexZero ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree a -> Maybe a
    indexTree 1 0 (Leaf x) = Just x
    indexTree _ _ (Leaf _) = Nothing
    indexTree _ 0 (Node x _ _) = Just x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
        in if offset <= halfSize
           then indexTree halfSize (offset - 1) t1
           else indexTree halfSize (offset - 1 - halfSize) t2

-- 1-based
unsafeIndexOne :: RAList a -> Word64 -> a
unsafeIndexOne Nil _ = error "out of bounds"
unsafeIndexOne (BHead w t ts) !i =
    if i <= w
    then indexTree w i t
    else unsafeIndexOne ts (i-w)
  where
    indexTree :: Word64 -> Word64 -> Tree a -> a
    indexTree _ 0 _ = error "index zero"
    indexTree 1 1 (Leaf x) = x
    indexTree _ _ (Leaf _) = error "out of bounds"
    indexTree _ 1 (Node x _ _) = x
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
            offset' = offset - 1
        in if offset' <= halfSize
           then indexTree halfSize offset' t1
           else indexTree halfSize (offset' - halfSize) t2

{- Note [Optimizations of safeIndexOneCont]
Bangs in the local definitions of 'safeIndexOneCont' are needed to tell GHC that the functions are
strict in the 'Word64' argument, so that GHC produces workers operating on @Word64#@.

The function itself is CPS-ed, so that the arguments force the local definitions to be retained
within 'safeIndexOneCont' instead of being pulled out via full-laziness or some other optimization
pass. This ensures that when 'safeIndexOneCont' gets inlined, the local definitions appear directly
in the GHC Core, allowing GHC to inline the arguments of 'safeIndexOneCont' and transform the whole
thing into a beautiful recursive join point full of @Word64#@s, i.e. allocating very little if
anything at all.
-}

-- See Note [Optimizations of safeIndexOneCont].
safeIndexOneCont :: forall a b. b -> (a -> b) -> RAList a -> Word64 -> b
safeIndexOneCont z f = findTree where
    findTree :: RAList a -> Word64 -> b
    -- See Note [Optimizations of safeIndexOneCont].
    findTree Nil !_ = z
    findTree (BHead w t ts) i =
        if i <= w
        then indexTree w i t
        else findTree ts (i-w)

    indexTree :: Word64 -> Word64 -> Tree a -> b
    -- See Note [Optimizations of safeIndexOneCont].
    indexTree !w 1 t = case t of
        Node x _ _ -> f x
        Leaf x     -> if w == 1 then f x else z
    indexTree _ 0 _ = z -- "index zero"
    indexTree _ _ (Leaf _) = z
    indexTree treeSize offset (Node _ t1 t2) =
        let halfSize = unsafeShiftR treeSize 1 -- probably faster than `div w 2`
            offset' = offset - 1
        in if offset' <= halfSize
           then indexTree halfSize offset' t1
           else indexTree halfSize (offset' - halfSize) t2
{-# INLINE safeIndexOneCont #-}

-- 1-based
safeIndexOne :: RAList a -> Word64 -> Maybe a
safeIndexOne = safeIndexOneCont Nothing Just

instance RAL.RandomAccessList (RAList a) where
    type Element (RAList a) = a

    {-# INLINABLE empty #-}
    empty = Nil
    {-# INLINABLE cons #-}
    cons = Cons
    {-# INLINABLE uncons #-}
    uncons = uncons
    {-# INLINABLE length #-}
    length Nil             = 0
    length (BHead sz _ tl) = sz + RAL.length tl
    {-# INLINABLE indexZero #-}
    indexZero = safeIndexZero
    {-# INLINABLE indexOne #-}
    indexOne = safeIndexOne
    {-# INLINABLE unsafeIndexZero #-}
    unsafeIndexZero = unsafeIndexZero
    {-# INLINABLE unsafeIndexOne #-}
    unsafeIndexOne = unsafeIndexOne
