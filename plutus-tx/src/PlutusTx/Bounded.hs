{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Bounded (Bounded (..), deriveBounded) where

import PlutusTx.Bool
import PlutusTx.Bounded.Class
import PlutusTx.Bounded.TH
import PlutusTx.Ord

deriveBounded ''Bool
deriveBounded ''Ordering
deriveBounded ''()
deriveBounded ''(,)
deriveBounded ''(,,)
deriveBounded ''(,,,)
deriveBounded ''(,,,,)
deriveBounded ''(,,,,,)
deriveBounded ''(,,,,,,)
deriveBounded ''(,,,,,,,)
deriveBounded ''(,,,,,,,,)
deriveBounded ''(,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveBounded ''(,,,,,,,,,,,,,,,,,,,,,,,,,,)
