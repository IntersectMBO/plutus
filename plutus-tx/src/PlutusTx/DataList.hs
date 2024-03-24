{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataList (

) where

import PlutusTx.AsData qualified as AsData
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (map)

import GHC.Exts qualified as H

AsData.asData
  [d|
    data List a = Nil | Cons a (List a)
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

type DataElem a = (P.UnsafeFromData a, P.ToData a)

instance (DataElem a) => H.IsList (List a) where
    type Item (List a) = a
    fromList [] = Nil
    fromList (x : xs) =
      Cons x (H.fromList xs)
    toList Nil         = []
    toList (Cons x xs) = x : H.toList xs

(.:) :: (DataElem a) => a -> List a -> List a
(.:) = Cons

-- empty List is overloaded as []

-- examples of using overloaded syntax

example0 :: DataElem a => List a
example0 = []

example1 :: List Bool
example1 = [True, False]

example2 :: List Integer
example2 = [1..10]

-- examples of using overloaded pattern matching
isSingleton :: DataElem a => List a -> Bool
isSingleton [_] = True
isSingleton _   = False

map :: (DataElem a, DataElem b) => (a -> b) -> List a -> List b
map _ []                   = []
-- unfortunately matching on ':' doesn't work
map f (H.toList -> x : xs) = f x .: map f (H.fromList xs)
