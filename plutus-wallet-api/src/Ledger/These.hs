{-# LANGUAGE TemplateHaskell #-}
-- A version of 'Data.These' that can be used in on-chain and off-chain code.
module Ledger.These(
    These(..)
  , these
  , theseWithDefault
  ) where

import           Ledger.These.TH (These (..))
import qualified Ledger.These.TH as TH

-- | See 'Ledger.These.TH.these'
these :: (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
these = $$(TH.these)

-- | See 'Ledger.These.TH.theseWithDefault
theseWithDefault :: a -> b -> (a -> b -> c) -> These a b -> c
theseWithDefault = $$(TH.theseWithDefault)
