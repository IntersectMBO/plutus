{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TemplateHaskell  #-}
{-

An effect for getting the current slot number

-}
module Plutus.PAB.Effects.TimeEffect(
    TimeEffect(..),
    systemTime
    ) where

import           Control.Monad.Freer.TH (makeEffect)
import           Ledger.Slot            (Slot)

data TimeEffect r where
    SystemTime :: TimeEffect Slot

makeEffect ''TimeEffect
