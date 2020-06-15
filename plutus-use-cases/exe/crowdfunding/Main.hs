-- | Contract interface for the crowdfunding contract
module Main where

import           Language.Plutus.Contract                              (ContractError)
import qualified Language.Plutus.Contract.App                          as App
import           Language.PlutusTx.Coordination.Contracts.Crowdfunding (crowdfunding, successfulCampaign, theCampaign)

main :: IO ()
main = App.runWithTraces (crowdfunding theCampaign)
        [ ("success-w1", (App.Wallet 1, successfulCampaign))
        , ("success-w2", (App.Wallet 2, successfulCampaign))
        , ("success-w3", (App.Wallet 3, successfulCampaign))
        , ("success-w4", (App.Wallet 4, successfulCampaign))
        ]
