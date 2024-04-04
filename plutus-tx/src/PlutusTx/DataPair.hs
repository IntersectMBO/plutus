{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataPair where

import Control.DeepSeq (NFData)
import Data.Data (Data)
import GHC.Generics (Generic)
import PlutusTx.AsData qualified as AsData
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude hiding (fst, snd)
import Prelude qualified as H

AsData.asData
  [d|
    data Pair a b = Pair a b
      deriving stock (Generic, Data, H.Show)
      deriving anyclass (NFData)
      deriving newtype (Eq) -- todo fix?
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

type DataElem a = (P.UnsafeFromData a, P.ToData a)

fst :: (DataElem a, DataElem b) => Pair a b -> a
fst (Pair a _) = a

snd :: (DataElem a, DataElem b) => Pair a b -> b
snd (Pair _ b) = b

map :: (DataElem a, DataElem b, DataElem c) => (b -> c) -> Pair a b -> Pair a c
map f (Pair a b) = Pair a (f b)
