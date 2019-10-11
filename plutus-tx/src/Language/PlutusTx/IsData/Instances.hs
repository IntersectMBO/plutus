{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.PlutusTx.IsData.Instances where

import           Prelude                     (Bool (..), Either (..), Maybe (..))

import           Language.PlutusTx.IsData.TH

makeIsData ''Bool
makeIsData ''()
makeIsData ''(,)
makeIsData ''Maybe
makeIsData ''Either
