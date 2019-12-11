{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module CrowdFundingSimulations where

import           CrowdFunding          (Contribution (Contribution), contribValue, registeredKnownCurrencies)
import qualified Ledger.Ada            as Ada
import           Playground.Types      (ContractCall (AddBlocks), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [basicCrowdFunding]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    wallet3 = Wallet {getWallet = 3}
    wallet4 = Wallet {getWallet = 4}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 30 <$>
        [wallet1, wallet2, wallet3, wallet4]
    basicCrowdFunding =
        Simulation
            { simulationName = "Basic Campaign"
            , simulationWallets
            , simulationActions =
                  [ scheduleCollection wallet1
                  , contribute wallet2 11
                  , contribute wallet3 10
                  , contribute wallet4 9
                  , AddBlocks 5
                  , AddBlocks 35
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
