{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataMap where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataList
import PlutusTx.DataPair (DataElem, Pair)
import PlutusTx.DataPair qualified as DPair
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude

AsData.asData
  [d|
    data Map k v = Map (List (Pair k v))
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

empty :: (DataElem k, DataElem v) => Map k v
empty = Map Nil

lookup :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Maybe v
lookup k (Map l) = go l
  where
    go Nil = Nothing
    go (Cons x xs)
        | k == DPair.fst x = Just . DPair.snd $ x
        | otherwise = go xs

member :: (DataElem k, DataElem v, Eq k) => k -> Map k v -> Bool
member k m =
    case lookup k m of
        Just _  -> True
        Nothing -> False
