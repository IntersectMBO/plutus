{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE ViewPatterns    #-}

module PlutusTx.DataList (

) where

import PlutusTx.Builtins qualified as P
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (map)

import GHC.Exts qualified as H

newtype List a = List P.BuiltinData

instance P.ToData (List a) where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (List l) = l

instance P.FromData (List a) where
  fromBuiltinData = Just . List

instance P.UnsafeFromData (List a) where
  unsafeFromBuiltinData = List

type DataElem a = (P.UnsafeFromData a, P.ToData a)

instance (P.UnsafeFromData a, P.ToData a) => H.IsList (List a) where
    type Item (List a) = a
    fromList = List . BI.mkList . go
      where
        go [] = BI.mkNilData BI.unitval
        go (x : xs) =
            BI.mkCons (P.toBuiltinData x) (go xs)
    toList (List l) = go . BI.unsafeDataAsList $ l
      where
        go xs =
            P.matchList
                xs
                []
                (\hd tl -> P.unsafeFromBuiltinData hd : go tl)

-- cons
(.:) :: (DataElem a) => a -> List a -> List a
(.:) x xs = H.fromList $ x : H.toList xs

-- empty List is overloaded as []

-- examples of using overloaded syntax

example0 :: (DataElem a) => List a
example0 = []

example1 :: List Bool
example1 = [True, False]

example2 :: List Integer
example2 = [1..10]

-- examples of using overloaded pattern matching
isSingleton :: (DataElem a) => List a -> Bool
isSingleton [a] = True
isSingleton _   = False

map :: (DataElem a, DataElem b) => (a -> b) -> List a -> List b
map _ []                   = []
-- unfortunately matching on ':' doesn't work
map f (H.toList -> x : xs) = f x .: map f (H.fromList xs)
