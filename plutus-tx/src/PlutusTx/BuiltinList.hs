{-# LANGUAGE LambdaCase #-}

-- | Functions operating on `BuiltinList`.
module PlutusTx.BuiltinList (
  BuiltinList,
  B.caseList,
  B.caseList',
  map,
  elem,
  find,
  any,
  all,
  (!!),
)
where

import Prelude (Bool (..), Integer, Maybe (..), otherwise, (.))

import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.HasOpaque
import PlutusTx.Builtins.Internal (BuiltinList)
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Eq
import PlutusTx.ErrorCodes
import PlutusTx.Trace (traceError)

infixl 9 !!

map :: forall a b. (MkNil b) => (a -> b) -> BuiltinList a -> BuiltinList b
map f = go
 where
  go :: BuiltinList a -> BuiltinList b
  go =
    B.caseList'
      B.mkNil
      (\x -> BI.mkCons (f x) . go)
{-# INLINEABLE map #-}

elem :: forall a. (Eq a) => a -> BuiltinList a -> Bool
elem a = go
 where
  go :: BuiltinList a -> Bool
  go = B.caseList' False (\x xs -> if a == x then True else go xs)
{-# INLINEABLE elem #-}

find :: forall a. (a -> Bool) -> BuiltinList a -> Maybe a
find p = go
 where
  go :: BuiltinList a -> Maybe a
  go =
    B.caseList'
      Nothing
      (\x xs -> if p x then Just x else go xs)
{-# INLINEABLE find #-}

any :: forall a. (a -> Bool) -> BuiltinList a -> Bool
any p = go
 where
  go :: BuiltinList a -> Bool
  go = B.caseList' False (\x xs -> if p x then True else go xs)
{-# INLINEABLE any #-}

all :: forall a. (a -> Bool) -> BuiltinList a -> Bool
all p = go
 where
  go :: BuiltinList a -> Bool
  go = B.caseList' True (\x xs -> if p x then go xs else False)
{-# INLINEABLE all #-}

{-| Get the element at a given index.

This function is partial and takes linear time.
-}
(!!) :: forall a. BuiltinList a -> Integer -> a
(!!) xs0 i0
  | i0 `B.lessThanInteger` 0 = traceError builtinListNegativeIndexError
  | otherwise = go xs0 i0
 where
  go :: BuiltinList a -> Integer -> a
  go xs i =
    B.caseList
      (\_ -> traceError builtinListIndexTooLargeError)
      ( \y ys _ ->
          if i `B.equalsInteger` 0
            then y
            else go ys (B.subtractInteger i 1)
      )
      xs
      ()
