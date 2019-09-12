-- | Contract interface for the crowdfunding contract
module Main where

import qualified Language.Plutus.Contract.App                          as App
import           Language.PlutusTx.Coordination.Contracts.CrowdFunding (crowdfunding, successfulCampaign, theCampaign)

main :: IO ()
main = App.runWithTraces (crowdfunding theCampaign)
        [ ("success-w1", (App.Wallet 1, successfulCampaign))
        , ("success-w2", (App.Wallet 2, successfulCampaign))
        , ("success-w3", (App.Wallet 3, successfulCampaign))
        , ("success-w4", (App.Wallet 4, successfulCampaign))
        ]
