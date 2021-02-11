{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.PlutusTx.IsData.Instances where

import           Prelude                     (Bool (..), Either (..), Maybe (..))

import           Language.PlutusTx.IsData.TH

-- While these types should be stable, we really don't want them changing, so index
-- them explicitly to be sure.
makeIsDataIndexed ''Bool [('False,0),('True,1)]
makeIsDataIndexed ''Maybe [('Just,0),('Nothing,1)]
makeIsDataIndexed ''Either [('Left,0),('Right,1)]

-- Okay to use unstableMakeIsData here since there's only one alternative and we're sure that will never change
unstableMakeIsData ''()
unstableMakeIsData ''(,)
unstableMakeIsData ''(,,)
unstableMakeIsData ''(,,,)
