{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module ErrorHandlingSimulations where

import           Data.Text             (Text)
import           ErrorHandling         (registeredKnownCurrencies)
import           Playground.Types      (Simulation (Simulation), SimulatorAction, simulationActions, simulationIndex,
                                        simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [throwCatch]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100 <$> [wallet1, wallet2]
    throwCatch =
        Simulation
            { simulationName = "Throw/Catch"
            , simulationIndex = 1
            , simulationWallets
            , simulationActions = [throwError wallet1, catchError wallet2]
            }

throwError :: Wallet -> SimulatorAction
throwError caller = callEndpoint @Text caller "throwError" "Hello"

catchError :: Wallet -> SimulatorAction
catchError caller = callEndpoint @Text caller "catchError" "World"
