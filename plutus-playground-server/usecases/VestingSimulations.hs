{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module VestingSimulations where

import           Ledger.Ada            (lovelaceValueOf)
import           Ledger.Value          (Value)
import           Playground.Types      (ContractCall (AddBlocks), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Vesting               (registeredKnownCurrencies)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [vestRetrieve]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100 <$> [wallet1, wallet2]
    vestRetrieve =
        Simulation
            { simulationName = "Vest/Retrieve"
            , simulationWallets
            , simulationActions =
                  [ vestFunds wallet2
                  , AddBlocks 20
                  , retrieveFunds wallet1 (lovelaceValueOf 4)
                  , AddBlocks 40
                  , retrieveFunds wallet1 (lovelaceValueOf 4)
                  , AddBlocks 1
                  ]
            }

vestFunds :: Wallet -> SimulatorAction
vestFunds caller = callEndpoint caller "vest funds" ()

retrieveFunds :: Wallet -> Value -> SimulatorAction
retrieveFunds caller = callEndpoint caller "retrieve funds"
