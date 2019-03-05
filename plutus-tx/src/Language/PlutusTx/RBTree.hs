{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- Otherwise we get specializations inside our unfoldings, and the specialisations
-- lack unfoldings themselves!
{-# OPTIONS_GHC -fno-spec-constr #-}
-- Otherwise we get tuple type reps, which we can't deal with
{-# OPTIONS_GHC -fno-strictness #-}
-- | This module defines a red-black tree suitable for use as a map or set.
--
-- The code is heavily inspired by the @llrbtree@ Haskell library, as well
-- as @https://github.com/sweirich/dth/blob/master/examples/red-black/RedBlack.lhs@.
-- However, this version has been modified significantly for TH usage and clarity.
--
-- This implementation also aims to be relatively elementary, since we don't have
-- features like GADTs which some implementations use to improve safety.
--
-- As a reminder, red-black trees have a number of invariants (some of the things that
-- are normally enforced as invariants are here ensured by the types):
-- (1) The root is black.
-- (2) If a node is red, then both its children are black.
-- (3) Every path from a given node to any of its leaves has the same number of
--     black nodes.
-- Invariant (2) and (3) between them ensure that the tree is balanced.
module Language.PlutusTx.RBTree (
    RBTree(..),
    Color(..),
    Comparison,
    empty,
    singleton,
    lookup,
    keys,
    values,
    toList,
    fromList,
    size,
    map,
    foldr,
    valid,
    insert,
    --delete,
    union,
    unionWith,
    unionThese,
    all,
    any)
where

import           Language.PlutusTx.Prelude    hiding (map, foldr, lookup, all, any)
import qualified Language.PlutusTx.Prelude    as P
import           Language.PlutusTx.These
import           Language.PlutusTx.Lift
import           Codec.Serialise
import           GHC.Generics

type Comparison k = k -> k -> Ordering

data Color = B | R
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise)

-- | The number of black nodes between this node and the leaves. Invariant (3) states
-- that this is the same for all paths, so can be represented with a single value.
type BlackHeight = Integer

data RBTree k v = Leaf | Branch Color BlackHeight (RBTree k v) k v (RBTree k v)
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise)

makeLift ''Color
makeLift ''RBTree

------------------------------------------------------------
-- Straightforward functions
------------------------------------------------------------

{-# INLINABLE empty #-}
empty :: RBTree k v
empty = Leaf

{-# INLINABLE singleton #-}
singleton :: k -> v -> RBTree k v
singleton k v = Branch B 1 Leaf k v Leaf

{-# INLINABLE blackHeight #-}
blackHeight :: RBTree k v -> BlackHeight
blackHeight = \case { Leaf -> 0 ; Branch _ h _ _ _ _ -> h }

{-# INLINABLE color #-}
color :: RBTree k v -> Color
color = \case { Leaf -> B ; Branch c _ _ _ _ _ -> c }

{-# INLINABLE lookup #-}
lookup :: Comparison k -> k -> RBTree k v -> Maybe v
lookup comp k =
    let go = \case
            Leaf -> Nothing
            Branch _ _ l k' v r -> case comp k k' of
                LT -> go l
                GT -> go r
                EQ -> Just v
    in go

{-# INLINABLE size #-}
size :: RBTree k v -> Integer
size t = length $ keys t

-- eta-expanded to avoid value restriction
{-# INLINABLE keys #-}
keys :: RBTree k v -> [k]
keys t = foldr (\(k,_) ks -> k:ks) [] t

-- eta-expanded to avoid value restriction
{-# INLINABLE values #-}
values :: RBTree k v -> [v]
values t = foldr (\(_,v) vs -> v:vs) [] t

-- eta-expanded to avoid value restriction
{-# INLINABLE toList #-}
toList :: RBTree k v -> [(k, v)]
toList t = foldr (\m ms -> m:ms) [] t

{-# INLINABLE fromList #-}
fromList :: Comparison k -> [(k, v)] -> RBTree k v
fromList comp entries = P.foldr (\(k, v) m -> insert comp k v m) empty entries

{-# INLINABLE map #-}
map :: (a -> b) -> RBTree k a -> RBTree k b
map f = \case
    Leaf -> Leaf
    Branch c h l k v r -> Branch c h (map f l) k (f v) (map f r)

{-# INLINABLE foldr #-}
foldr :: ((k, v) -> b -> b) -> b -> RBTree k v -> b
foldr f acc = \case
    Leaf -> acc
    Branch _ _ l k v r ->
        let
            right = foldr f acc r
            center = f (k, v) right
            left = foldr f center l
        in left

------------------------------------------------------------
-- Invariants and validity
------------------------------------------------------------

{-# INLINABLE isBalanced #-}
isBalanced :: RBTree k v -> Bool
isBalanced t = sameBlacksToLeaves t && checkChildren t

{-# INLINABLE sameBlacksToLeaves #-}
sameBlacksToLeaves :: RBTree k v -> Bool
sameBlacksToLeaves t = case blacksToLeaves t of
    [] -> True
    n:ns -> P.all (eq n) ns

{-# INLINABLE blacksToLeaves #-}
blacksToLeaves :: RBTree k v -> [Integer]
blacksToLeaves =
    let blacksToLeavesFrom :: Integer -> RBTree k v -> [Integer]
        blacksToLeavesFrom n = \case
          Leaf -> [n `plus` 1]
          Branch R _ l _ _ r -> blacksToLeavesFrom n l ++ blacksToLeavesFrom n r
          Branch B _ l _ _ r -> blacksToLeavesFrom (n `plus` 1) l ++ blacksToLeavesFrom (n `plus` 1) r
    in blacksToLeavesFrom 0

{-# INLINABLE checkChildren #-}
checkChildren :: RBTree k v -> Bool
checkChildren t =
    let
        checkVsParentColor _ Leaf = True
        -- Red child of red parent - invariant violation!
        checkVsParentColor R (Branch R _ _ _ _ _) = False
        checkVsParentColor _ (Branch c _ l _ _ r) = checkVsParentColor c l && checkVsParentColor c r
    in checkVsParentColor (color t) t

{-# INLINABLE keysSorted #-}
keysSorted :: Comparison k -> RBTree k v -> Bool
keysSorted comp t =
    let sorted [] = True
        sorted [_] = True
        sorted (x:y:xys) = case comp x y of
            LT -> sorted (y:xys)
            _ -> False
    in sorted $ keys t

{-# INLINABLE correctBlackHeight #-}
correctBlackHeight :: RBTree k v -> Bool
correctBlackHeight t =
    let correct n Leaf = n `eq` 0
        correct n (Branch R h l _ _ r) = n `eq` h' && correct n l && correct n r
          where h' = h `minus` 1
        correct n (Branch B h l _ _ r) = n `eq` h && correct n' l && correct n' r
          where n' = n `minus` 1
    in correct (blackHeight t) t

{-# INLINABLE valid #-}
valid :: Comparison k -> RBTree k v -> Bool
valid comp t = isBalanced t && correctBlackHeight t && keysSorted comp t

------------------------------------------------------------
-- Colour switching
------------------------------------------------------------

{-# INLINABLE redden #-}
redden :: RBTree k v -> RBTree k v
redden = \case { Leaf -> Leaf; Branch _ h l k v r -> Branch R h l k v r }

{-# INLINABLE blacken #-}
blacken :: RBTree k v -> RBTree k v
blacken = \case { Leaf -> Leaf; Branch _ h l k v r -> Branch B h l k v r }

------------------------------------------------------------
-- Insertion and balancing
------------------------------------------------------------

{-# INLINABLE insert #-}
insert :: Comparison k -> k -> v -> RBTree k v -> RBTree k v
insert comp k v t =
    let go = \case
            Leaf -> Branch R 1 Leaf k v Leaf
            (Branch B h l k' v' r) -> case comp k k' of
                LT -> balanceL (Branch B h (go l) k' v' r)
                GT -> balanceR (Branch B h l k' v' (go r))
                EQ -> Branch B h l k' v r
            (Branch R h l k' v' r) -> case comp k k' of
                LT -> Branch R h (go l) k' v' r
                GT -> Branch R h l k' v' (go r)
                EQ -> Branch R h l k' v r
    in blacken (go t)

{- Note [Balancing]
There are four cases for (locally) balancing a subtree, each of which
produces the same top-level pattern, visible on the right-hand sides
of each of the cases below.

The cases split into those that balance the left side, and those that
balance the right side. Often we know that only one side can be unbalanced,
so it is advantageous to run only one side.

L1:
          B3           R2
         /  \         /  \
        R2   T  ->   B1  B3
       /  \         / \  / \
      R1   T        T T  T T
     /  \
    T    T

L2:
        B3             R2
       /  \           /  \
      R1   T    ->   B1  B3
     /  \           / \  / \
    T    R2         T T  T T
        /  \
       T    T

R1:
      B1               R2
     /  \             /  \
    T   R2      ->   B1  B3
       /  \         / \  / \
      T   R1        T T  T T
         /  \
        T    T

R2:
      B1               R2
     /  \             /  \
    T   R2      ->   B1  B3
       /  \         / \  / \
      R1   T        T T  T T
     /  \
    T    T
-}

{-# INLINABLE balanceL #-}
-- | Correct a local imbalance on the left side of the tree.
balanceL :: RBTree k v -> RBTree k v
balanceL t = case t of
    Branch B h toSplit k3 v3 t4 -> case toSplit of
        -- See note [Balancing], this is case L1
        Branch R _ (Branch R _ t1 k1 v1 t2) k2 v2 t3 ->
            Branch R (h `plus` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        -- See note [Balancing], this is case L2
        Branch R _ t1 k1 v1 (Branch R _ t2 k2 v2 t3) ->
            Branch R (h `plus` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        _ -> t
    _ -> t

{-# INLINABLE balanceR #-}
-- | Correct a local imbalance on the right side of the tree.
balanceR :: RBTree k v -> RBTree k v
balanceR t = case t of
    Branch B h t1 k1 v1 toSplit -> case toSplit of
        -- See note [Balancing], this is case R1
        Branch R _ t2 k2 v2 (Branch R _ t3 k3 v3 t4) ->
            Branch R (h `plus` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        -- See note [Balancing], this is case R2
        Branch R _ (Branch R _ t2 k2 v2 t3) k3 v3 t4 ->
            Branch R (h `plus` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        _ -> t
    _ -> t

------------------------------------------------------------
-- Joining and splitting
------------------------------------------------------------

{-# INLINABLE join #-}
-- | Join two trees, with a key-value mapping in the middle. The keys in the
-- left tree are assumed to be less than the key in the middle, which is less than the
-- keys in the right tree.
join :: Comparison k -> k -> v -> RBTree k v -> RBTree k v -> RBTree k v
join comp k v =
    let join Leaf t2 = insert comp k v t2
        join t1 Leaf = insert comp k v t1
        join t1 t2 = case compareInteger h1 h2 of
            LT -> blacken $ joinLT t1 t2 h1
            GT -> blacken $ joinGT t1 t2 h2
            EQ -> blacken $ joinEQ t1 t2 h1
          where
            h1 = blackHeight t1
            h2 = blackHeight t2

        joinLT t1 t2@(Branch c h l k' v' r) h1
          | h `eq` h1   = joinEQ t1 t2 h
          | otherwise = balanceL (Branch c h (joinLT t1 l h1) k' v' r)
        joinLT t1 Leaf _ = t1

        joinGT t1@(Branch c h l k' v' r) t2 h2
          | h `eq` h2   = joinEQ t1 t2 h
          | otherwise = balanceR (Branch c h l k' v' (joinGT r t2 h2))
        joinGT Leaf t2 _ = t2

        joinEQ t1 t2 h = Branch R (h `plus` 1) t1 k v t2
    in join

{-# INLINABLE split #-}
-- | Given a key @k@, spits a tree into a left tree with keys less than @k@, optionally a value
-- corresponding to the mapping for @k@ if there is one, and a right tree with keys greater
-- than @k@.
split :: Comparison k -> k -> RBTree k v -> (RBTree k v, Maybe v, RBTree k v)
split comp needle =
    let jn = join comp
        go = \case
            Leaf -> (Leaf, Nothing, Leaf)
            Branch _ _ l k v r -> case comp needle k of
                LT -> let (l', mid, r') = go l in (l', mid, jn k v r' (blacken r))
                GT -> let (l', mid, r') = go r in (jn k v (blacken l) l', mid, r')
                EQ -> (blacken l, Just v, blacken r)
    in go

------------------------------------------------------------
-- Union
------------------------------------------------------------

{-# INLINABLE unionThese #-}
-- | Union two trees, keeping both values for a key in case it appears on both sides.
-- This is the most general union function, but it is less efficient than 'unionWith'
-- and 'union'.
unionThese :: Comparison k -> RBTree k a -> RBTree k b -> RBTree k (These a b)
unionThese comp =
    -- The cases for leaves meant that this is less efficient than a simple union:
    -- it must look at every element (this is obvious from the type!).
    let union l Leaf = blacken $ map This l
        union Leaf r = blacken $ map That r
        union (Branch _ _ l k v r) t =
            -- There are several ways to do a union of RBTree. This way has the
            -- key advantage of pulling out the mapping for k if there is one,
            -- so we can package it up in a 'These' properly.
            let (l', maybeV, r') = split comp k t
                theseVs = andMaybe v maybeV
            in join comp k theseVs (union l l') (union r r')
    in union

{-# INLINABLE unionWith #-}
-- | Union two trees, using the given function to compute a value when a key has a
-- mapping on both sides.
unionWith :: Comparison k -> (a -> a -> a) -> RBTree k a -> RBTree k a -> RBTree k a
unionWith comp with =
    let union l Leaf = blacken l
        union Leaf r = blacken r
        union (Branch _ _ l k v r) t =
            let (l', maybeV, r') = split comp k t
                newV = case maybeV of
                    Just v' -> with v v'
                    Nothing -> v
            in join comp k newV (union l l') (union r r')
    in union

{-# INLINABLE union #-}
-- | Left-biased union of two trees.
union :: Comparison k -> RBTree k a -> RBTree k a -> RBTree k a
union comp = unionWith comp (\a _ -> a)

------------------------------------------------------------
-- Deletion
------------------------------------------------------------

{-
delete :: Q (TExp (Comparison k -> k -> RBTree k v -> RBTree k v))
delete = [|| \comp k t -> let (l, _, r) =  $$split comp k t in $$join comp l r ||]
-}

------------------------------------------------------------
-- Derived operations
------------------------------------------------------------

-- eta-expanded to avoid value restriction
{-# INLINABLE all #-}
all :: (v -> Bool) -> RBTree k v -> Bool
all p t = foldr (\(_, v) acc -> p v && acc) True t

-- eta-expanded to avoid value restriction
{-# INLINABLE any #-}
any :: (v -> Bool) -> RBTree k v -> Bool
any p t = foldr (\(_, v) acc -> p v || acc) False t
