{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module PlutusTx.Ord (Ord (..), Ordering (..), deriveOrd) where

import PlutusTx.Bool
import PlutusTx.Either
import PlutusTx.Ord.Class
import PlutusTx.Ord.TH
import Prelude (Maybe (..))

deriveOrd ''[]
deriveOrd ''Bool
deriveOrd ''Maybe
deriveOrd ''Either
deriveOrd ''Ordering
deriveOrd ''()
deriveOrd ''(,)
-- TODO: enable when deriveEq is merge 
-- deriveOrd ''(,,)
-- deriveOrd ''(,,,)
-- deriveOrd ''(,,,,)
-- deriveOrd ''(,,,,,)
-- deriveOrd ''(,,,,,,)
-- deriveOrd ''(,,,,,,,)
-- deriveOrd ''(,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,,,,,)
-- deriveOrd ''(,,,,,,,,,,,,,,,,,,,,,,,,,,)
