{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- Otherwise we get specializations inside our unfoldings, and the specialisations
-- lack unfoldings themselves!
{-# OPTIONS_GHC -fno-spec-constr #-}
-- Otherwise we get tuple type reps, which we can't deal with
{-# OPTIONS_GHC -fno-strictness #-}
{-# LANGUAGE DeriveDataTypeable    #-}
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
module PlutusTx.RBTree (
    RBTree(..),
    Color(..),
    empty,
    singleton,
    lookup,
    keys,
    values,
    toList,
    fromList,
    size,
    foldr,
    mapThese,
    valid,
    insert,
    --delete,
    union,
    unionWith,
    unionThese,
    biFoldr,
    all,
    allMappings,
    any,
    anyMappings)
where

import Codec.Serialise
import Control.DeepSeq
import Data.Data (Data)
import GHC.Generics
import PlutusTx.Builtins
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData
import PlutusTx.Lift
import PlutusTx.Prelude hiding (all, any, foldr, map, toList)
import PlutusTx.Prelude qualified as P
import PlutusTx.These
import Prelude qualified as Haskell

type Comparison k = k -> k -> Ordering

data Color = B | R
    deriving stock (Haskell.Show, Haskell.Eq, Haskell.Ord, Generic, Data)
    deriving anyclass (Serialise, NFData)

-- | The number of black nodes between this node and the leaves. Invariant (3) states
-- that this is the same for all paths, so can be represented with a single value.
type BlackHeight = Integer

data RBTree k v = Leaf | Branch Color BlackHeight (RBTree k v) k v (RBTree k v)
    deriving stock (Generic, Data)
    deriving anyclass (Serialise, NFData)

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
lookup :: Ord k => k -> RBTree k v -> Maybe v
lookup k =
    let go = \case
            Leaf -> Nothing
            Branch _ _ l k' v r -> case compare k k' of
                LT -> go l
                GT -> go r
                EQ -> Just v
    in go

{-# INLINABLE size #-}
size :: RBTree k v -> Integer
size t = length $ keys t

{-# INLINABLE keys #-}
keys :: RBTree k v -> [k]
keys = foldr (\k _ ks -> k:ks) []

{-# INLINABLE values #-}
values :: RBTree k v -> [v]
values = foldr (\_ v vs -> v:vs) []

{-# INLINABLE toList #-}
toList :: RBTree k v -> [(k, v)]
toList = foldr (\k v ms -> (k, v):ms) []

{-# INLINABLE fromList #-}
fromList :: Ord k => [(k, v)] -> RBTree k v
fromList = P.foldr (\(k, v) m -> insert k v m) empty

instance Functor (RBTree k) where
  fmap f = go
    where
      go = \case
        Leaf -> Leaf
        Branch c h l k v r -> Branch c h (go l) k (f v) (go r)
  {-# INLINABLE fmap #-}

{-# INLINABLE foldr #-}
foldr :: (k -> v -> b -> b) -> b -> RBTree k v -> b
foldr f = go
  where
    go acc = \case
      Leaf -> acc
      Branch _ _ l k v r -> go (f k v (go acc r)) l

{-# INLINEABLE mapThese #-}
-- | A version of 'Data.Map.Lazy.mapEither' that works with 'These'.
mapThese :: (Ord k) => (v -> These a b) -> RBTree k v -> (RBTree k a, RBTree k b)
mapThese f mp = (fromList mpl, fromList mpr)
  where
    (mpl, mpr) = P.foldr f' ([], []) (toList $ fmap f mp)
    f' (k, v) (as, bs) = case v of
      This a    -> ((k, a) : as, bs)
      That b    -> (as, (k, b) : bs)
      These a b -> ((k, a) : as, (k, b) : bs)

------------------------------------------------------------
-- Invariants and validity
------------------------------------------------------------

{-# INLINABLE isBalanced #-}
isBalanced :: RBTree k v -> Bool
isBalanced t = sameBlacksToLeaves t && checkChildren t

{-# INLINABLE sameBlacksToLeaves #-}
sameBlacksToLeaves :: RBTree k v -> Bool
sameBlacksToLeaves t = case blacksToLeaves t of
    []   -> True
    n:ns -> P.all (equalsInteger n) ns

{-# INLINABLE blacksToLeaves #-}
blacksToLeaves :: RBTree k v -> [Integer]
blacksToLeaves =
    let blacksToLeavesFrom :: Integer -> RBTree k v -> [Integer]
        blacksToLeavesFrom n = \case
          Leaf -> [n `addInteger` 1]
          Branch R _ l _ _ r -> blacksToLeavesFrom n l ++ blacksToLeavesFrom n r
          Branch B _ l _ _ r ->
            blacksToLeavesFrom (n `addInteger` 1) l ++ blacksToLeavesFrom (n `addInteger` 1) r
    in blacksToLeavesFrom 0

{-# INLINABLE checkChildren #-}
checkChildren :: RBTree k v -> Bool
checkChildren t =
    let
        checkVsParentColor _ Leaf                 = True
        -- Red child of red parent - invariant violation!
        checkVsParentColor R (Branch R _ _ _ _ _) = False
        checkVsParentColor _ (Branch c _ l _ _ r) = checkVsParentColor c l && checkVsParentColor c r
    in checkVsParentColor (color t) t

{-# INLINABLE keysSorted #-}
keysSorted :: Ord k => RBTree k v -> Bool
keysSorted t =
    let sorted [] = True
        sorted [_] = True
        sorted (x:y:xys) = case compare x y of
            LT -> sorted (y:xys)
            _  -> False
    in sorted $ keys t

{-# INLINABLE correctBlackHeight #-}
correctBlackHeight :: RBTree k v -> Bool
correctBlackHeight t =
    let correct n Leaf = n `equalsInteger` 0
        correct n (Branch R h l _ _ r) = n `equalsInteger` h' && correct n l && correct n r
          where h' = h `subtractInteger` 1
        correct n (Branch B h l _ _ r) = n `equalsInteger` h && correct n' l && correct n' r
          where n' = n `subtractInteger` 1
    in correct (blackHeight t) t

{-# INLINABLE valid #-}
valid :: Ord k => RBTree k v -> Bool
valid t = isBalanced t && correctBlackHeight t && keysSorted t

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
insert :: Ord k => k -> v -> RBTree k v -> RBTree k v
insert k v t =
    let go = \case
            Leaf -> Branch R 1 Leaf k v Leaf
            (Branch B h l k' v' r) -> case compare k k' of
                LT -> balanceL (Branch B h (go l) k' v' r)
                GT -> balanceR (Branch B h l k' v' (go r))
                EQ -> Branch B h l k' v r
            (Branch R h l k' v' r) -> case compare k k' of
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
            Branch R (h `addInteger` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        -- See note [Balancing], this is case L2
        Branch R _ t1 k1 v1 (Branch R _ t2 k2 v2 t3) ->
            Branch R (h `addInteger` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        _ -> t
    _ -> t

{-# INLINABLE balanceR #-}
-- | Correct a local imbalance on the right side of the tree.
balanceR :: RBTree k v -> RBTree k v
balanceR t = case t of
    Branch B h t1 k1 v1 toSplit -> case toSplit of
        -- See note [Balancing], this is case R1
        Branch R _ t2 k2 v2 (Branch R _ t3 k3 v3 t4) ->
            Branch R (h `addInteger` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        -- See note [Balancing], this is case R2
        Branch R _ (Branch R _ t2 k2 v2 t3) k3 v3 t4 ->
            Branch R (h `addInteger` 1) (Branch B h t1 k1 v1 t2) k2 v2 (Branch B h t3 k3 v3 t4)
        _ -> t
    _ -> t

------------------------------------------------------------
-- Joining and splitting
------------------------------------------------------------

{-# INLINABLE join #-}
-- | Join two trees, with a key-value mapping in the middle. The keys in the
-- left tree are assumed to be less than the key in the middle, which is less than the
-- keys in the right tree.
join :: Ord k => k -> v -> RBTree k v -> RBTree k v -> RBTree k v
join k v =
    let join Leaf t2 = insert k v t2
        join t1 Leaf = insert k v t1
        join t1 t2 = case compare h1 h2 of
            LT -> blacken $ joinLT t1 t2 h1
            GT -> blacken $ joinGT t1 t2 h2
            EQ -> blacken $ joinEQ t1 t2 h1
          where
            h1 = blackHeight t1
            h2 = blackHeight t2

        joinLT t1 t2@(Branch c h l k' v' r) h1
          | h `equalsInteger` h1   = joinEQ t1 t2 h
          | otherwise = balanceL (Branch c h (joinLT t1 l h1) k' v' r)
        joinLT t1 Leaf _ = t1

        joinGT t1@(Branch c h l k' v' r) t2 h2
          | h `equalsInteger` h2   = joinEQ t1 t2 h
          | otherwise = balanceR (Branch c h l k' v' (joinGT r t2 h2))
        joinGT Leaf t2 _ = t2

        joinEQ t1 t2 h = Branch R (h `addInteger` 1) t1 k v t2
    in join

{-# INLINABLE split #-}
-- | Given a key @k@, spits a tree into a left tree with keys less than @k@, optionally a value
-- corresponding to the mapping for @k@ if there is one, and a right tree with keys greater
-- than @k@.
split :: Ord k => k -> RBTree k v -> (RBTree k v, Maybe v, RBTree k v)
split needle =
    let go = \case
            Leaf -> (Leaf, Nothing, Leaf)
            Branch _ _ l k v r -> case compare needle k of
                LT -> let (l', mid, r') = go l in (l', mid, join k v r' (blacken r))
                GT -> let (l', mid, r') = go r in (join k v (blacken l) l', mid, r')
                EQ -> (blacken l, Just v, blacken r)
    in go

------------------------------------------------------------
-- Union
------------------------------------------------------------

{-# INLINABLE union #-}
-- | Union two trees, keeping both values for a key in case it appears on both sides.
-- This is the most general union function, but it is less efficient than 'unionWith'
-- and 'union'.
union :: Ord k => RBTree k a -> RBTree k b -> RBTree k (These a b)
union =
    -- The cases for leaves meant that this is less efficient than a simple union:
    -- it must look at every element (this is obvious from the type!).
    let union l Leaf = blacken $ fmap This l
        union Leaf r = blacken $ fmap That r
        union (Branch _ _ l k v r) t =
            -- There are several ways to do a union of RBTree. This way has the
            -- key advantage of pulling out the mapping for k if there is one,
            -- so we can package it up in a 'These' properly.
            let (l', maybeV, r') = split k t
                theseVs = andMaybe v maybeV
            in join k theseVs (union l l') (union r r')
    in union

{-# INLINABLE unionWith #-}
-- | Union two trees, using the given function to compute a value when a key has a
-- mapping on both sides.
unionWith :: Ord k => (a -> a -> a) -> RBTree k a -> RBTree k a -> RBTree k a
unionWith with =
    let union l Leaf = blacken l
        union Leaf r = blacken r
        union (Branch _ _ l k v r) t =
            let (l', maybeV, r') = split k t
                newV = case maybeV of
                    Just v' -> with v v'
                    Nothing -> v
            in join k newV (union l l') (union r r')
    in union

{-# INLINABLE unionThese #-}
-- | Union two trees, using the given function to compute a value.
unionThese :: forall k a b c . Ord k => (These a b -> c) -> RBTree k a -> RBTree k b -> RBTree k c
unionThese f = go
  where
    fL v = f (This v)
    fR v = f (That v)
    go :: RBTree k a -> RBTree k b -> RBTree k c
    go l Leaf = blacken $ fmap fL l
    go Leaf r = blacken $ fmap fR r
    go (Branch _ _ l k v r) rt =
          let (l', maybeV, r') = split k rt
          in join k (f (v `andMaybe` maybeV)) (go l l') (go r r')

biFoldr
  :: forall k a b c
  . Ord k
  => (k -> These a b -> c -> c)
  -> c
  -> RBTree k a -> RBTree k b -> c
biFoldr f z = go z
  where
    fL k v = f k (This v)
    fR k v = f k (That v)
    go :: c -> RBTree k a -> RBTree k b -> c
    go acc l Leaf = foldr fL acc l
    go acc Leaf r = foldr fR acc r
    go acc (Branch _ _ l k v r) rt =
          let (l', maybeV, r') = split k rt
          in go (f k (v `andMaybe` maybeV) (go acc r r')) l l'

--{-# INLINABLE union #-}
-- | Left-biased union of two trees.
--union :: Ord k => RBTree k a -> RBTree k a -> RBTree k a
--union = unionWith (\a _ -> a)

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

{-# INLINABLE allMappings #-}
allMappings :: (k -> v -> Bool) -> RBTree k v -> Bool
allMappings p = foldr (\k v acc -> p k v && acc) True

{-# INLINABLE all #-}
all :: (v -> Bool) -> RBTree k v -> Bool
all p = allMappings (\_ v -> p v)

{-# INLINABLE anyMappings #-}
anyMappings :: (k -> v -> Bool) -> RBTree k v -> Bool
anyMappings p = foldr (\k v acc -> p k v || acc) False

{-# INLINABLE any #-}
any :: (v -> Bool) -> RBTree k v -> Bool
any p = anyMappings (\_ v -> p v)

instance Eq Color where
  R == R = True
  B == B = True
  _ == _ = False

instance (Eq k, Eq v) => Eq (RBTree k v) where
  Leaf == Leaf = True
  Branch c h l k v r == Branch c' h' l' k' v' r' =
    c == c' && h == h' && l == l' && k == k' && v == v' && r == r'
  _ == _ = False

instance (Haskell.Show k, Haskell.Show v) => Haskell.Show (RBTree k v) where
  show t = Haskell.show $ toList t

-- Hand-written instances to use the underlying 'Map' type in 'Data', and
-- to be reasonably efficient.
instance (ToData k, ToData v) => ToData (RBTree k v) where
  toBuiltinData m = BI.mkMap (mapToBuiltin $ toList m)
    where
      {-# INLINE mapToBuiltin #-}
      mapToBuiltin :: [(k, v)] -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
      mapToBuiltin = go
        where
          go :: [(k, v)] -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
          go []            = BI.mkNilPairData BI.unitval
          go ((k, v) : xs) = BI.mkCons (BI.mkPairData (toBuiltinData k) (toBuiltinData v)) (go xs)

instance (Ord k, FromData k, FromData v) => FromData (RBTree k v) where
  fromBuiltinData d =
    matchData'
      d
      (\_ _ -> Nothing)
      (\es -> traverseFromBuiltin es)
      (const Nothing)
      (const Nothing)
      (const Nothing)
    where
      {-# INLINE traverseFromBuiltin #-}
      traverseFromBuiltin ::
        BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) ->
        Maybe (RBTree k v)
      traverseFromBuiltin = go empty
        where
          go ::
            RBTree k v
            -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
            -> Maybe (RBTree k v)
          go acc l =
            matchList
              l
              (pure acc)
              (\h t -> case (fromBuiltinData $ BI.fst h, fromBuiltinData $ BI.snd h) of
                    (Just k, Just v) -> go (insert k v acc) t
                    _                -> Nothing
              )

instance (Ord k, UnsafeFromData k, UnsafeFromData v) => UnsafeFromData (RBTree k v) where
  -- The `~` here enables `BI.unsafeDataAsMap d` to be inlined, which reduces costs slightly.
  -- Without the `~`, the inliner would consider it not effect safe to inline.
  -- We can remove the `~` once we make the inliner smart enough to inline them.
  -- See https://github.com/input-output-hk/plutus/pull/5371#discussion_r1297833685
  unsafeFromBuiltinData d = let ~es = BI.unsafeDataAsMap d in mapFromBuiltin es
    where
      {-# INLINE mapFromBuiltin #-}
      mapFromBuiltin :: BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData) -> RBTree k v
      mapFromBuiltin = go empty
        where
          go ::
            RBTree k v
            -> BI.BuiltinList (BI.BuiltinPair BI.BuiltinData BI.BuiltinData)
            -> RBTree k v
          go acc l =
            matchList
              l
              acc
              (\h t ->
                 let acc' = insert
                       (unsafeFromBuiltinData $ BI.fst h) (unsafeFromBuiltinData $ BI.snd h) acc
                 in go acc' t
              )
