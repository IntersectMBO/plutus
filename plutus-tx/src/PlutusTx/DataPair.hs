{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataPair where

import PlutusTx.AsData qualified as AsData
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude qualified as Prelude

AsData.asData
  [d|
    data Pair a b = Pair a b
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]
