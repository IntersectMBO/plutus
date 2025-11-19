{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Eq (Eq (..), (/=), deriveEq) where

import PlutusTx.Eq.Class
import PlutusTx.Eq.TH
import PlutusTx.Bool
import PlutusTx.Either (Either (..))
import Prelude (Maybe (..), Ordering (..))

deriveEq ''[]
deriveEq ''Bool
deriveEq ''Maybe
deriveEq ''Either
deriveEq ''Ordering
deriveEq ''()
deriveEq ''(,)
deriveEq ''(,,)
deriveEq ''(,,,)
deriveEq ''(,,,,)
deriveEq ''(,,,,,)
deriveEq ''(,,,,,,)
deriveEq ''(,,,,,,,)
deriveEq ''(,,,,,,,,)
deriveEq ''(,,,,,,,,,)
deriveEq ''(,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveEq ''(,,,,,,,,,,,,,,,,,,,,,,,,,,)
