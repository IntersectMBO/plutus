{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}

module CrowdfundingSimulations where

import           Crowdfunding          (Contribution (Contribution), contribValue, registeredKnownCurrencies)
import qualified Ledger.Ada            as Ada
import           Playground.Types      (ContractCall (AddBlocksUntil), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationId, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Wallet.Emulator.Types (WalletNumber (..))

simulations :: [Simulation]
simulations = [basicCrowdfunding]
  where
    wallet1 = WalletNumber 1
    wallet2 = WalletNumber 2
    wallet3 = WalletNumber 3
    wallet4 = WalletNumber 4
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100_000_000 <$>
        [wallet1, wallet2, wallet3, wallet4]
    basicCrowdfunding =
        Simulation
            { simulationName = "Basic Campaign"
            , simulationId = 1
            , simulationWallets
            , simulationActions =
                  [ scheduleCollection wallet1
                  , contribute wallet2 11_000_000
                  , contribute wallet3 10_000_000
                  , contribute wallet4 90_000_000
                  , AddBlocksUntil 41
                  ]
            }

scheduleCollection :: WalletNumber -> SimulatorAction
scheduleCollection caller = callEndpoint caller "schedule collection" ()

contribute :: WalletNumber -> Integer -> SimulatorAction
contribute caller lovelace =
    callEndpoint
        caller
        "contribute"
        Contribution {contribValue = Ada.lovelaceValueOf lovelace}
