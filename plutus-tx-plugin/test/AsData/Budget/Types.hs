{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ViewPatterns        #-}

module AsData.Budget.Types where

import PlutusTx.AsData qualified as AsData
import PlutusTx.IsData qualified as PlutusTx
import PlutusTx.Prelude qualified as PlutusTx

AsData.asData
  [d|
    data Ints = Ints
      { int1 :: Integer
      , int2 :: Integer
      , int3 :: Integer
      , int4 :: Integer
      }
      deriving newtype (PlutusTx.Eq, PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]
