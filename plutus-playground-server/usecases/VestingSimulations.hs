{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings  #-}

module VestingSimulations where

import           Ledger.Ada            (lovelaceValueOf)
import           Ledger.Value          (Value)
import           Playground.Types      (ContractCall (AddBlocks), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationId, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Vesting               (registeredKnownCurrencies)
import           Wallet.Emulator.Types (WalletNumber (..))

simulations :: [Simulation]
simulations = [vestRetrieve]
  where
    wallet1 = WalletNumber 1
    wallet2 = WalletNumber 2
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100_000_000 <$> [wallet1, wallet2]
    vestRetrieve =
        Simulation
            { simulationName = "Vest/Retrieve"
            , simulationId = 1
            , simulationWallets
            , simulationActions =
                  [ vestFunds wallet2
                  , AddBlocks 20
                  , retrieveFunds wallet1 (lovelaceValueOf 40_000_000)
                  , AddBlocks 40
                  , retrieveFunds wallet1 (lovelaceValueOf 40_000_000)
                  , AddBlocks 1
                  ]
            }

vestFunds :: WalletNumber -> SimulatorAction
vestFunds caller = callEndpoint caller "vest funds" ()

retrieveFunds :: WalletNumber -> Value -> SimulatorAction
retrieveFunds caller = callEndpoint caller "retrieve funds"
