-- | Contract interface for the crowdfunding contract
module Main where

import qualified Language.Plutus.Contract.App                          as App
import           Language.PlutusTx.Coordination.Contracts.CrowdFunding (crowdfunding)

main :: IO ()
main = App.run crowdfunding
