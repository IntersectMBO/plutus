{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

module IsData.Budget.Lib where

import PlutusTx.Prelude

import PlutusTx.IsData (unstableMakeIsData)
import PlutusTx.Lift (makeLift)

data Single = Single Integer

unstableMakeIsData ''Single
makeLift ''Single

data Pair = PairA Integer | PairB Integer

unstableMakeIsData ''Pair
makeLift ''Pair

data Mixed = MNone | MOne Integer | MTwo Integer Integer

unstableMakeIsData ''Mixed
makeLift ''Mixed

data ABC = A Integer | B Integer | C Integer

unstableMakeIsData ''ABC
makeLift ''ABC
