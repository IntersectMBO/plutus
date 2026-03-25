{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module IsData.Budget.Lib where

import PlutusTx.IsData (unstableMakeIsData)
import PlutusTx.Lift (makeLift)

data ABC = A Integer | B Integer | C Integer

unstableMakeIsData ''ABC
makeLift ''ABC
