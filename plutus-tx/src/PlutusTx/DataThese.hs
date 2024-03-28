{-# LANGUAGE ConstraintKinds    #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.DataThese where

import PlutusTx.AsData qualified as AsData
import PlutusTx.DataPair (DataElem)
import PlutusTx.IsData qualified as P
import PlutusTx.Prelude

AsData.asData
  [d|
    data These a b
        = This a
        | That b
        | These a b
      deriving newtype (Eq) -- todo fix?
      deriving newtype (P.ToData, P.FromData, P.UnsafeFromData)
  |]

theseWithDefault :: (DataElem a, DataElem b) => a -> b -> (a -> b -> c) -> These a b -> c
theseWithDefault a' b' f = \case
    This a    -> f a b'
    That b    -> f a' b
    These a b -> f a b

these :: (DataElem a, DataElem b) => (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these f g h = \case
    This a    -> f a
    That b    -> g b
    These a b -> h a b
