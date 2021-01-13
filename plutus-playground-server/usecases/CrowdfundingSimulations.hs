{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module CrowdfundingSimulations where

import           Crowdfunding          (Contribution (Contribution), contribValue, registeredKnownCurrencies)
import qualified Ledger.Ada            as Ada
import           Playground.Types      (ContractCall (AddBlocksUntil), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationIndex, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [basicCrowdfunding]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    wallet3 = Wallet {getWallet = 3}
    wallet4 = Wallet {getWallet = 4}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 30 <$>
        [wallet1, wallet2, wallet3, wallet4]
    basicCrowdfunding =
        Simulation
            { simulationName = "Basic Campaign"
            , simulationIndex = 1
            , simulationWallets
            , simulationActions =
                  [ scheduleCollection wallet1
                  , contribute wallet2 11
                  , contribute wallet3 10
                  , contribute wallet4 9
                  , AddBlocksUntil 41
                  ]
            }

scheduleCollection :: Wallet -> SimulatorAction
scheduleCollection caller = callEndpoint caller "schedule collection" ()

contribute :: Wallet -> Integer -> SimulatorAction
contribute caller lovelace =
    callEndpoint
        caller
        "contribute"
        Contribution {contribValue = Ada.lovelaceValueOf lovelace}
