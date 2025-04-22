{-# LANGUAGE LambdaCase #-}

-- | Functions operating on `BuiltinList`.
module PlutusTx.BuiltinList (
  BuiltinList,
  B.caseList,
  B.caseList',
  B.null,
  B.uncons,
  map,
  elem,
  find,
  any,
  all,
  (!!),
)
where

import Prelude (Bool (..), Integer, Maybe (..), const, curry, id, not, otherwise, undefined, (.))

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.HasOpaque
import PlutusTx.Builtins.Internal (BuiltinList, BuiltinPair)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Eq
import PlutusTx.ErrorCodes
import PlutusTx.Ord
import PlutusTx.Trace (traceError)


-- | Plutus Tx version of 'Data.List.map' for 'BuiltinList'.
map :: forall a b. (MkNil b) => (a -> b) -> BuiltinList a -> BuiltinList b
map f = go
  where
    go :: BuiltinList a -> BuiltinList b
    go = B.caseList' B.mkNil ( \x xs -> f x `BI.mkCons` go xs )
{-# INLINEABLE map #-}

-- | Plutus Tx version of 'Data.List.mapMaybe' for 'BuiltinList'.
mapMaybe :: forall a b. (MkNil b) => (a -> Maybe b) -> BuiltinList a -> BuiltinList b
mapMaybe f = go
  where
    go :: BuiltinList a -> BuiltinList b
    go = B.caseList' B.mkNil
      ( \x xs -> case f x of
          Nothing -> go xs
          Just y  -> y `BI.mkCons` go xs
      )
{-# INLINEABLE mapMaybe #-}

-- | Does the element occur in the list?
elem :: forall a. (Eq a) => a -> BuiltinList a -> Bool
elem a = go
  where
    go :: BuiltinList a -> Bool
    go = B.caseList' False ( \x xs -> if a == x then True else go xs )
{-# INLINEABLE elem #-}

-- | Returns the leftmost element matching the predicate, or `Nothing` if there's no such element.
find :: forall a. (a -> Bool) -> BuiltinList a -> Maybe a
find p = go
  where
    go :: BuiltinList a -> Maybe a
    go = B.caseList' Nothing ( \x xs -> if p x then Just x else go xs )
{-# INLINEABLE find #-}

-- | Determines whether any element of the structure satisfies the predicate.
any :: forall a. (a -> Bool) -> BuiltinList a -> Bool
any p = go
  where
    go :: BuiltinList a -> Bool
    go = B.caseList' False ( \x xs -> if p x then True else go xs )
{-# INLINEABLE any #-}

-- | Determines whether all elements of the list satisfy the predicate.
all :: forall a. (a -> Bool) -> BuiltinList a -> Bool
all p = go
  where
    go :: BuiltinList a -> Bool
    go = B.caseList' True ( \x xs -> if p x then go xs else False )
{-# INLINEABLE all #-}

-- | Plutus Tx version of '(GHC.List.!!)' for 'BuiltinList'.
-- This function is partial and takes linear time.
infixl 9 !!
(!!) :: forall a. BuiltinList a -> Integer -> a
(!!) xs0 i0
  | i0 `B.lessThanInteger` 0 = traceError builtinListNegativeIndexError
  | otherwise = go i0 xs0
 where
  go :: Integer -> BuiltinList a ->  a
  go i = B.caseList'
    (traceError builtinListIndexTooLargeError)
    ( \y ys ->
        if i `B.equalsInteger` 0
        then y
        else go (B.subtractInteger i 1) ys
    )
{-# INLINEABLE (!!) #-}

-- TODO add tests and changelog for Data.List

-- | Plutus Tx version of 'Data.List.length' for 'BuiltinList'.
length :: forall a. BuiltinList a -> Integer
length = foldr ( \_ -> B.addInteger 1 ) 0
{-# INLINABLE length #-}

-- | Returns the conjunction of a list of Bools.
and :: BuiltinList Bool -> Bool
and = all id

-- | Returns the disjunction of a list of Bools.
or :: BuiltinList Bool -> Bool
or = any id
{-# INLINABLE or #-}

-- | The negation of `elem`.
notElem :: forall a. (Eq a) => a -> BuiltinList a -> Bool
notElem a = not . elem a
{-# INLINABLE notElem #-}

-- | Plutus Tx version of 'Data.List.foldr' for 'BuiltinList'.
foldr :: forall a b. (a -> b -> b) -> b -> BuiltinList a -> b
foldr f acc = go
  where
    go :: BuiltinList a -> b
    go = B.caseList' acc ( \x xs -> f x (go xs) )
{-# INLINABLE foldr #-}

-- | Plutus Tx velsion of 'Data.List.foldl' for 'BuiltinList'.
foldl :: forall a b. (b -> a -> b) -> b -> BuiltinList a -> b
foldl f = go
  where
    go :: b -> BuiltinList a -> b
    go acc = B.caseList' acc ( \x xs -> go (f acc x) xs )
{-# INLINABLE foldl #-}

-- | Plutus Tx version of '(Data.List.++)' for 'BuiltinList'.
infixr 5 ++
(++) :: forall a. BuiltinList a -> BuiltinList a -> BuiltinList a
(++) l r = foldr BI.mkCons r l
{-# INLINABLE (++) #-}

-- | Plutus Tx version of 'Data.List.concat' for 'BuiltinList'.
concat :: forall a. (MkNil a) => BuiltinList (BuiltinList a) -> BuiltinList a
concat = foldr (++) B.mkNil
{-# INLINABLE concat #-}

-- | Plutus Tx version of 'Data.List.concatMap' for 'BuiltinList'.
concatMap :: forall a b. (MkNil b) => (a -> BuiltinList b) -> BuiltinList a -> BuiltinList b
concatMap f = foldr ( \x ys -> f x ++ ys ) B.mkNil
{-# INLINABLE concatMap #-}

-- | Plutus Tx version of 'Data.List.filter' for 'BuiltinList'.
filter :: forall a. (MkNil a) => (a -> Bool) -> BuiltinList a -> BuiltinList a
filter p = foldr ( \x xs -> if p x then x `BI.mkCons` xs else xs ) B.mkNil
{-# INLINABLE filter #-}

-- | Plutus Tx version of 'Data.List.listToMaybe' for 'BuiltinList'.
listToMaybe :: forall a. BuiltinList a -> Maybe a
listToMaybe = BI.caseList' Nothing ( \x _ -> Just x )
{-# INLINABLE listToMaybe #-}

-- | Return the element in the list, if there is precisely one.
uniqueElement :: forall a. BuiltinList a -> Maybe a
uniqueElement = BI.caseList' Nothing
  ( \x -> BI.caseList' (Just x) ( \_ _ -> Nothing )
  )
{-# INLINABLE uniqueElement #-}

-- | Plutus Tx version of 'Data.List.findIndices' for 'BuiltinList'.
findIndices :: forall a. (a -> Bool) -> BuiltinList a -> BuiltinList Integer
findIndices p = go 0
  where
    go :: Integer -> BuiltinList a -> BuiltinList Integer
    go i = BI.caseList' B.mkNil
      ( \x xs ->
          let indices = go (B.addInteger i 1) xs
          in if p x then BI.mkCons i indices else indices
      )
{-# INLINABLE findIndices #-}

-- | Plutus Tx version of 'Data.List.findIndex'.
findIndex :: forall a. (a -> Bool) -> BuiltinList a -> Maybe Integer
findIndex f = go 0
  where
    go :: Integer -> BuiltinList a -> Maybe Integer
    go i = BI.caseList' Nothing
      ( \x xs -> if f x then Just i else go (B.addInteger i 1) xs
      )
{-# INLINABLE findIndex #-}

-- | Cons each element of the first list to the second one in reverse order
-- (i.e. the last element of the first list is the head of the result).
--
-- > revAppend xs ys === reverse xs ++ ys
revAppend :: forall a. BuiltinList a -> BuiltinList a -> BuiltinList a
revAppend l r = BI.caseList' r ( \x xs -> revAppend xs (x `BI.mkCons` r) ) l
{-# INLINABLE revAppend #-}

-- | Plutus Tx version of 'Data.List.reverse' for 'BuiltinList'.
reverse :: forall a. (MkNil a) => BuiltinList a -> BuiltinList a
reverse xs = revAppend xs B.mkNil
{-# INLINABLE reverse #-}

-- | Plutus Tx version of 'Data.List.zip' for 'BuiltinList'.
zip
  :: forall a b. (MkNil a, MkNil b)
  => BuiltinList a
  -> BuiltinList b
  -> BuiltinList (BuiltinPair a b)
zip = zipWith (curry BI.BuiltinPair)
{-# INLINABLE zip #-}

-- | Plutus Tx version of 'Data.List.unzip' for 'BuiltinList'.
unzip
  :: forall a b. (MkNil a, MkNil b)
  => BuiltinList (BuiltinPair a b)
  -> BuiltinPair (BuiltinList a) (BuiltinList b)
unzip = B.caseList' emptyPair
  ( \p l -> do
      let BI.BuiltinPair (x, y) = p
      let BI.BuiltinPair (xs', ys') = unzip l
      BI.BuiltinPair (x `BI.mkCons` xs', y `BI.mkCons` ys')
  )
  where
    emptyPair :: BuiltinPair (BuiltinList a) (BuiltinList b)
    emptyPair = BI.BuiltinPair (B.mkNil, B.mkNil)
{-# INLINABLE unzip #-}

-- | Plutus Tx version of 'Data.List.head' for 'BuiltinList'.
head :: forall a. BuiltinList a -> a
head = B.caseList' (traceError headEmptyBuiltinListError) ( \x _ -> x )
{-# INLINABLE head #-}

-- | Plutus Tx version of 'Data.List.last' for 'BuiltinList'.
last :: forall a. BuiltinList a -> a
last = B.caseList' (traceError lastEmptyBuiltinListError)
  ( \x -> B.caseList' x ( \_ -> last )
  )
{-# INLINABLE last #-}

-- | Plutus Tx version of 'Data.List.tail' for 'BuiltinList'.
tail :: forall a. BuiltinList a -> BuiltinList a
tail = B.caseList' (traceError lastEmptyBuiltinListError) ( \_ xs -> xs )
{-# INLINABLE tail #-}

-- | Plutus Tx version of 'Data.List.take' for 'BuiltinList'.
take :: forall a. (MkNil a) => Integer -> BuiltinList a -> BuiltinList a
take n l
  | n `B.lessThanInteger` 0 = B.mkNil
  | otherwise = B.caseList' B.mkNil
      ( \x xs -> x `BI.mkCons` take (B.subtractInteger n 1) xs
      ) l
{-# INLINABLE take #-}

-- | Plutus Tx version of 'Data.List.drop' for 'BuiltinList'.
drop :: forall a. (MkNil a) => Integer -> BuiltinList a -> BuiltinList a
drop n l
  | n `B.lessThanEqualsInteger` 0 = B.mkNil
  | otherwise = B.caseList' B.mkNil
      ( \_ xs -> drop (B.subtractInteger n 1) xs
      ) l
{-# INLINABLE drop #-}

-- -- | Plutus Tx version of 'Data.List.splitAt'.
-- splitAt :: forall a. Integer -> BuiltinList a -> BuiltinPair (BuiltinList a) (BuiltinList a)
-- splitAt n xs
--   | n `B.lessThanEqualInteger` 0 = BI.BuiltinPair (B.mkNil, xs)
--   | otherwise = go n xs
--   where
--     go :: Integer -> BuiltinList a -> (BuiltinList a, BuiltinList a)
--     go m = B.caseList' (BI.BuiltinPair (B.mkNil, B.mkNil)) (\x xs ->
--       if m `B.equalsInteger` 0
--         then BI.BuiltinPair (B.mkNil, xs)
--         else let BI.BuiltinPair (zs, ws) = go (B.subtractInteger m 1) xs
--              in BI.BuiltinPair (BI.mkCons x zs, ws)
--     )


--     []     = ([], [])
--     go m (y:ys)
--       | m == 1 = ([y], ys)
--       | otherwise = case go (Builtins.subtractInteger m 1) ys of
--           (zs, ws) -> (y:zs, ws)
-- {-# INLINABLE splitAt #-}

-- | Plutus Tx version of 'Data.List.nub' for 'BuiltinList'.
nub :: forall a. (Eq a, MkNil a) => BuiltinList a -> BuiltinList a
nub = nubBy (==)
{-# INLINABLE nub #-}

-- | Plutus Tx version of 'Data.List.elemBy' for 'BuiltinList'.
elemBy :: forall a. (a -> a -> Bool) -> a -> BuiltinList a -> Bool
elemBy eq y = go
  where
    go :: BuiltinList a -> Bool
    go = B.caseList' False ( \x xs -> if eq x y then True else go xs )
{-# INLINABLE elemBy #-}

-- | Plutus Tx version of 'Data.List.nubBy' for 'BuiltinList'.
nubBy :: forall a. (MkNil a) => (a -> a -> Bool) -> BuiltinList a -> BuiltinList a
nubBy eq = go B.mkNil
  where
    go :: BuiltinList a -> BuiltinList a -> BuiltinList a
    go xs = B.caseList' B.mkNil
      ( \y ys ->
          if elemBy eq y xs
          then go xs ys
          else y `BI.mkCons` go ys (y `BI.mkCons` xs)
      )
{-# INLINABLE nubBy #-}

-- | Plutus Tx version of 'Data.List.zipWith' for 'BuiltinList'.
zipWith
  :: forall a b c. (MkNil c)
  => (a -> b -> c)
  -> BuiltinList a
  -> BuiltinList b
  -> BuiltinList c
zipWith f = go
  where
    go :: BuiltinList a -> BuiltinList b -> BuiltinList c
    go xs ys =
      B.caseList' B.mkNil
        ( \x xs' ->
            B.caseList' B.mkNil
              ( \y ys' -> f x y `BI.mkCons` go xs' ys'
              ) ys
        ) xs
{-# INLINABLE zipWith #-}

-- | Plutus Tx version of 'Data.List.dropWhile' for 'BuiltinList'.
dropWhile :: forall a. (MkNil a) => (a -> Bool) -> BuiltinList a -> BuiltinList a
dropWhile p = go
  where
    go :: BuiltinList a -> BuiltinList a
    go xs = B.caseList' B.mkNil ( \x xs' -> if p x then go xs' else xs ) xs
{-# INLINABLE dropWhile #-}

-- | Plutus Tx version of 'Data.List.replicate' for 'BuiltinList'.
replicate :: forall a. (MkNil a) => Integer -> a -> BuiltinList a
replicate n0 x = go n0
  where
    go :: Integer -> BuiltinList a
    go n
      | n `B.lessThanEqualsInteger` 0 = B.mkNil
      | otherwise = x `BI.mkCons` go (B.subtractInteger n 1)
{-# INLINABLE replicate #-}

-- | Plutus Tx version of 'Data.List.partition' for 'BuiltinList'.
partition
  :: forall a. (MkNil a)
  => (a -> Bool)
  -> BuiltinList a
  -> BuiltinPair (BuiltinList a) (BuiltinList a)
partition p = BI.BuiltinPair . foldr select (B.mkNil, B.mkNil)
  where
    select :: a -> (BuiltinList a, BuiltinList a) -> (BuiltinList a, BuiltinList a)
    select x ~(ts, fs)
      | p x = (x `BI.mkCons` ts, fs)
      | otherwise = (ts, x `BI.mkCons` fs)
{-# INLINABLE partition #-}

-- -- | Plutus Tx version of 'Data.List.nubBy' for 'BuiltinList'.
-- nubByFast :: forall a. (MkNil a) => (a -> a -> Bool) -> BuiltinList a -> BuiltinList a
-- nubByFast eq = toBuiltinList (Prelude.nubBy eq (fromBuiltinList))
--   where
--     go :: BuiltinList a -> BuiltinList a -> BuiltinList a
--     go xs = B.caseList' B.mkNil
--       ( \y ys ->
--           if elemBy eq y xs then
--             go xs ys
--           else
--             y `BI.mkCons` go ys (y `BI.mkCons` xs)
--       )
-- {-# INLINABLE nubBy #-}
-- | Plutus Tx version of 'Data.List.sort'.
-- sort :: Ord a => BuiltinList a -> BuiltinList a
-- sort = sortBy compare
-- {-# INLINABLE sort #-}

-- sortBy = undefined
-- -- | Plutus Tx version of 'Data.List.sortBy'.
-- sortBy :: (a -> a -> Ordering) -> BuiltinList a -> BuiltinList a
-- sortBy cmp l = mergeAll (sequences l)
--   where
--     sequences (a:b:xs)
--       | a `cmp` b == GT = descending b BuiltinList a  xs
--       | otherwise       = ascending  b (a:) xs
--     sequences xs = [xs]

--     descending a as (b:bs)
--       | a `cmp` b == GT = descending b (a:as) bs
--     descending a as bs  = (a:as): sequences bs

--     ascending a as (b:bs)
--       | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
--     ascending a as bs   = let x = as BuiltinList a
--                           in x : sequences bs

--     mergeAll [x] = x
--     mergeAll xs  = mergeAll (mergePairs xs)

--     mergePairs (a:b:xs) = let x = merge a b
--                           in x : mergePairs xs
--     mergePairs xs       = xs

--     merge as@(a:as') bs@(b:bs')
--       | a `cmp` b == GT = b:merge as  bs'
--       | otherwise       = a:merge as' bs
--     merge [] bs         = bs
--     merge as []         = as
-- {-# INLINABLE sortBy #-}


-- -- append,
-- -- findIndices,
-- -- filter,
-- -- mapMaybe,
-- -- foldMap,
-- -- length,
-- -- mconcat,
-- -- (<|),
-- -- cons,
-- -- nil,
-- -- singleton,
-- -- uncons,
-- -- and,
-- -- or,
-- -- notElem,
-- -- foldr,
-- -- foldl,
-- -- concat,
-- -- concatMap,
-- -- listToMaybe,
-- -- uniqueElement,
-- -- revAppend,
-- -- reverse,
-- -- replicate,
-- -- findIndex,
-- -- unzip,
-- -- zipWith,
-- -- head,
-- -- last,
-- -- tail,
-- -- take,
-- -- drop,
-- -- dropWhile,
-- -- splitAt,
-- -- elemBy,
-- -- nubBy,
-- -- nub,
-- -- partition,
-- -- toBuiltinList,
-- -- fromBuiltinList,
-- -- toSOP,
-- -- fromSOP,
