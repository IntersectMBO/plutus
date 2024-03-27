{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataMap where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataList
import PlutusTx.DataPair
import PlutusTx.IsData qualified as P

AsData.asData
  [d|
    data Map k v = Map (List (Pair k v))
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]
