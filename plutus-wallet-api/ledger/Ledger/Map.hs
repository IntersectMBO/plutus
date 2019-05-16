{-# LANGUAGE TemplateHaskell #-}

-- A map implementation that can be used in on-chain and off-chain code.
module Ledger.Map(
    Map
    , IsEqual
    , singleton
    , empty
    , fromList
    , toList
    , keys
    , map
    , lookup
    , union
    , all
    -- * These
    , These(..)
    , these
    ) where

import           Ledger.Map.TH
import           Prelude       hiding (all, lookup, map)
