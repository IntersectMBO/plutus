{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataList where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataPair (DataElem)
import PlutusTx.Foldable qualified as Foldable
import PlutusTx.IsData qualified as P

AsData.asData
  [d|
    data List a = Nil | Cons a (List a)
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

fromList :: DataElem a => [a] -> List a
fromList = Foldable.foldr Cons Nil

foldr :: DataElem a => (a -> b -> b) -> b -> List a -> b
foldr _ u Nil         = u
foldr f u (Cons x xs) = f x (foldr f u xs)

toList :: DataElem a => List a -> [a]
toList = foldr (:) []
