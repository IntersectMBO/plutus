{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.Data.AssocList (
  AssocList,
  lookup,
  member,
  insert,
  delete,
  singleton,
  empty,
  null,
  toList,
  toBuiltinList,
  safeFromList,
  unsafeFromList,
  unsafeFromBuiltinList,
  uncons,
  unsafeUncons,
  noDuplicateKeys,
  all,
  any,
  union,
  unionWith,
  ) where

import PlutusTx.Builtins qualified as P
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (all, any, null, toList, uncons)
import PlutusTx.These

import Prelude qualified as Haskell

-- TODO: fix docs
{- | An associative map implementation backed by `P.BuiltinData`.

This map implementation has the following characteristics:

  * The `P.toBuiltinData` and `P.unsafeFromBuiltinData` operations are no-op.
  * Other operations are slower than @PlutusTx.AssocMap.Map@, although equality
    checks on keys can be faster due to `P.equalsData`.
  * Many operations involve converting the keys and/or values to/from `P.BuiltinData`.

Therefore this map implementation is likely a better choice than @PlutusTx.AssocMap.Map@
if it is part of a data type defined using @asData@, and the key and value types
have efficient `P.toBuiltinData` and `P.unsafeFromBuiltinData` operations (e.g., they
are primitive types or types defined using @asData@).
-}
newtype AssocList k a = AssocList P.BuiltinData
  deriving stock (Haskell.Eq, Haskell.Show)
  deriving newtype (Eq)

instance P.ToData (AssocList k a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (AssocList d) = d

instance P.FromData (AssocList k a) where
  fromBuiltinData = Just . AssocList

instance P.UnsafeFromData (AssocList k a) where
  unsafeFromBuiltinData = AssocList

{-# INLINEABLE lookup #-}
lookup :: forall k a. (P.ToData k, P.UnsafeFromData a) => k -> AssocList k a -> Maybe a
lookup (P.toBuiltinData -> k) m = case lookup' k (toBuiltinList m) of
  Just a  -> Just (P.unsafeFromBuiltinData a)
  Nothing -> Nothing

{-# INLINEABLE lookup' #-}
lookup' ::
  BuiltinData ->
  BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
  Maybe BuiltinData
lookup' k = go
  where
    go xs =
      P.matchList
        xs
        Nothing
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then Just (BI.snd hd)
                  else go tl
        )

{-# INLINEABLE member #-}
member :: forall k a. (P.ToData k) => k -> AssocList k a -> Bool
member (P.toBuiltinData -> k) m = member' k (toBuiltinList m)

{-# INLINEABLE member' #-}
member' :: BuiltinData -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
member' k = go
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        False
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then True
                  else go tl
        )

{-# INLINEABLE insert #-}
insert :: forall k a. (P.ToData k, P.ToData a) => k -> a -> AssocList k a -> AssocList k a
insert (P.toBuiltinData -> k) (P.toBuiltinData -> a) m =
  unsafeFromBuiltinList $ insert' k a (toBuiltinList m)

{-# INLINEABLE insert' #-}
insert'
  :: BuiltinData
  -> BuiltinData
  -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
  -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
insert' (P.toBuiltinData -> k) (P.toBuiltinData -> a) = go
  where
    go ::
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    go xs =
      P.matchList
        xs
        (BI.mkCons (BI.mkPairData k a) nil)
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then BI.mkCons (BI.mkPairData k a) tl
                  else BI.mkCons hd (go tl)
        )

{-# INLINEABLE delete #-}
delete :: forall k a. (P.ToData k) => k -> AssocList k a -> AssocList k a
delete (P.toBuiltinData -> k) m = unsafeFromBuiltinList (go (toBuiltinList m))
  where
    go ::
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
      BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    go xs =
      P.matchList
        xs
        nil
        ( \hd tl ->
            let k' = BI.fst hd
             in if P.equalsData k k'
                  then tl
                  else BI.mkCons hd (go tl)
        )

{-# INLINEABLE singleton #-}
singleton :: forall k a. (P.ToData k, P.ToData a) => k -> a -> AssocList k a
singleton (P.toBuiltinData -> k) (P.toBuiltinData -> a) = unsafeFromBuiltinList xs
  where
    xs = BI.mkCons (BI.mkPairData k a) nil

{-# INLINEABLE empty #-}
empty :: forall k a. AssocList k a
empty = unsafeFromBuiltinList nil

{-# INLINEABLE null #-}
null :: forall k a. AssocList k a -> Bool
null = P.null . toBuiltinList

{-# INLINEABLE safeFromList #-}
safeFromList :: forall k a . (Eq k, P.ToData k, P.ToData a) => [(k, a)] -> AssocList k a
safeFromList =
  unsafeFromBuiltinList
    . toBuiltin
    . PlutusTx.Prelude.map (\(k, a) -> (P.toBuiltinData k, P.toBuiltinData a))
    . foldr (uncurry go) []
  where
    go :: k -> a -> [(k, a)] -> [(k, a)]
    go k v [] = [(k,  v)]
    go k v ((k', v') : rest) =
      if k == k'
        then (k, v) : rest
        else (k', v') : go k v rest

{-# INLINEABLE unsafeFromList #-}
unsafeFromList :: (P.ToData k, P.ToData a) => [(k, a)] -> AssocList k a
unsafeFromList =
  unsafeFromBuiltinList
    . toBuiltin
    . PlutusTx.Prelude.map (\(k, a) -> (P.toBuiltinData k, P.toBuiltinData a))

{-# INLINEABLE uncons #-}
uncons ::
  forall k a.
  (P.UnsafeFromData k, P.UnsafeFromData a) =>
  AssocList k a ->
  Maybe ((k, a), AssocList k a)
uncons m = case P.uncons (toBuiltinList m) of
  Nothing -> Nothing
  Just (pair, rest) ->
    let (k, a) = P.pairToPair pair
     in Just ((P.unsafeFromBuiltinData k, P.unsafeFromBuiltinData a), unsafeFromBuiltinList rest)

{-# INLINEABLE unsafeUncons #-}
unsafeUncons ::
  forall k a.
  (P.UnsafeFromData k, P.UnsafeFromData a) =>
  AssocList k a ->
  ((k, a), AssocList k a)
unsafeUncons m =
  ((P.unsafeFromBuiltinData k, P.unsafeFromBuiltinData a), unsafeFromBuiltinList tl)
  where
    (hd, tl) = P.unsafeUncons (toBuiltinList m)
    (k, a) = P.pairToPair hd

{-# INLINEABLE noDuplicateKeys #-}
noDuplicateKeys :: forall k a. AssocList k a -> Bool
noDuplicateKeys m = go (toBuiltinList m)
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        True
        ( \hd tl ->
            let k = BI.fst hd
             in if member' k tl then False else go tl
        )

{-# INLINEABLE all #-}
all :: forall k a. (P.UnsafeFromData a) => (a -> Bool) -> AssocList k a -> Bool
all p m = go (toBuiltinList m)
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        True
        ( \hd tl ->
            let a = P.unsafeFromBuiltinData (BI.snd hd)
             in if p a then go tl else False
        )

{-# INLINEABLE any #-}
any :: forall k a. (P.UnsafeFromData a) => (a -> Bool) -> AssocList k a -> Bool
any p m = go (toBuiltinList m)
  where
    go :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> Bool
    go xs =
      P.matchList
        xs
        False
        ( \hd tl ->
            let a = P.unsafeFromBuiltinData (BI.snd hd)
             in if p a then True else go tl
        )

{-# INLINEABLE union #-}

-- TODO: This is broken!
-- The value should be a correct encoding of a `These` value, but it is not.
-- Example:
--  > union (safeFromList []) (safeFromList [(0, 0)]) :: AssocList Integer (These Integer Integer)
--  > AssocList Map [(I 0,I 0)]
-- The second element of the pair should be encoded as the appropriate `Constr`!
-- | Combine two 'AssocList's.
union ::
  forall k a b.
  (P.UnsafeFromData a, P.UnsafeFromData b, P.ToData a, P.ToData b) =>
  AssocList k a ->
  AssocList k b ->
  AssocList k (These a b)
union (toBuiltinList -> ls) (toBuiltinList -> rs) = unsafeFromBuiltinList res
  where
    goLeft xs =
      P.matchList
        xs
        nil
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
                v' = case lookup' k rs of
                  Just r ->
                    P.toBuiltinData
                      ( These
                          (P.unsafeFromBuiltinData v)
                          (P.unsafeFromBuiltinData r)
                        :: These a b
                      )
                  Nothing ->
                    P.toBuiltinData (This (P.unsafeFromBuiltinData v) :: These a b)
             in BI.mkCons (BI.mkPairData k v') (goLeft tl)
        )

    goRight xs =
      P.matchList
        xs
        nil
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
                v' = case lookup' k ls of
                  Just r ->
                    P.toBuiltinData
                      ( These
                          (P.unsafeFromBuiltinData v)
                          (P.unsafeFromBuiltinData r)
                        :: These a b
                      )
                  Nothing ->
                    P.toBuiltinData (That (P.unsafeFromBuiltinData v) :: These a b)
             in BI.mkCons (BI.mkPairData k v') (goRight tl)
        )

    res = goLeft ls `safeAppend` goRight rs

    safeAppend xs1 xs2 =
      P.matchList
        xs1
        xs2
        ( \hd tl ->
            let k = BI.fst hd
                v = BI.snd hd
             in insert' k v (safeAppend tl xs2)
        )

-- | Combine two 'AssocList's with the given combination function.
unionWith ::
  forall k a.
  (P.UnsafeFromData a, P.ToData a) =>
  (a -> a -> a) ->
  AssocList k a ->
  AssocList k a ->
  AssocList k a
unionWith f (toBuiltinList -> ls) (toBuiltinList -> rs) =
  unsafeFromBuiltinList res
  where
    ls' :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    ls' = go ls
      where
        go xs =
          P.matchList
            xs
            nil
            ( \hd tl ->
                let k' = BI.fst hd
                    v' = BI.snd hd
                    v'' = case lookup' k' rs of
                      Just r ->
                        P.toBuiltinData
                          (f (P.unsafeFromBuiltinData v') (P.unsafeFromBuiltinData r))
                      Nothing -> v'
                 in BI.mkCons (BI.mkPairData k' v'') (go tl)
            )

    rs' :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    rs' = go rs
      where
        go xs =
          P.matchList
            xs
            nil
            ( \hd tl ->
                let k' = BI.fst hd
                    tl' = go tl
                 in if member' k' ls
                      then tl'
                      else BI.mkCons hd tl'
            )

    res :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
    res = go rs' ls'
      where
        go acc xs =
          P.matchList
            xs
            acc
            (\hd -> go (BI.mkCons hd acc))

{-# INLINEABLE toList #-}

{- | `toList` is expensive since it traverses the whole map.
`toBuiltinList` is much faster.
-}
toList :: (P.UnsafeFromData k, P.UnsafeFromData a) => AssocList k a -> [(k, a)]
toList d = go (toBuiltinList d)
  where
    go xs =
      P.matchList
        xs
        []
        ( \hd tl ->
            (P.unsafeFromBuiltinData (BI.fst hd), P.unsafeFromBuiltinData (BI.snd hd))
              : go tl
        )

{-# INLINEABLE toBuiltinList #-}
toBuiltinList :: AssocList k a -> BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
toBuiltinList (AssocList d) = BI.unsafeDataAsMap d

{-# INLINEABLE unsafeFromBuiltinList #-}
unsafeFromBuiltinList ::
  forall k a.
  BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) ->
  AssocList k a
unsafeFromBuiltinList = AssocList . BI.mkMap

{-# INLINEABLE nil #-}
nil :: BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData)
nil = BI.mkNilPairData BI.unitval
