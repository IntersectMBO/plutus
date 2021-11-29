{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TemplateHaskell       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module PlutusTx.LiftU.Instances where

import PlutusTx.Bool (Bool (..))
import PlutusTx.Either (Either (..))
import PlutusTx.LiftU.TH
import PlutusTx.Maybe (Maybe (..))

defaultMakeLiftU ''Bool
defaultMakeLiftU ''Maybe
defaultMakeLiftU ''Either
defaultMakeLiftU ''[]
defaultMakeLiftU ''()
defaultMakeLiftU ''(,)
defaultMakeLiftU ''(,,)
defaultMakeLiftU ''(,,,)
