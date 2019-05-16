-- A version of 'Data.These' that can be used in on-chain and off-chain code.
module Ledger.These(
    These(..)
  , these
  , theseWithDefault
  ) where

import           Ledger.These.TH
