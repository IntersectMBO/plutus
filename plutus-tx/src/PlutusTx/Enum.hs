{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Enum (Enum (..), deriveEnum, deriveEnumData) where

import PlutusTx.Bool
import PlutusTx.Enum.Class
import PlutusTx.Enum.TH
import PlutusTx.Ord

deriveEnum ''Bool
deriveEnum ''()
deriveEnumData ''Ordering
