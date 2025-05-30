{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant if" #-}

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

This function throws an error if the index is negative or
larger than the length of the list.
-}
(!!) :: forall a. BuiltinList a -> Integer -> a
(!!) xs i
  | i `B.lessThanInteger` 0 = traceError builtinListNegativeIndexError
  | otherwise =
      B.caseList
        (\_ann -> traceError builtinListIndexTooLargeError)
        (\y _rest _ann -> y)
        (BI.drop i xs)
        ()
