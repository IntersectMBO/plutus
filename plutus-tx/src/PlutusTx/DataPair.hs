{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataPair where

import PlutusTx.AsData qualified as AsData
import PlutusTx.IsData qualified as P

AsData.asData
  [d|
    data Pair a b = Pair a b
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

type DataElem a = (P.UnsafeFromData a, P.ToData a)

fst :: (DataElem a, DataElem b) => Pair a b -> a
fst (Pair a _) = a

snd :: (DataElem a, DataElem b) => Pair a b -> b
snd (Pair _ b) = b
