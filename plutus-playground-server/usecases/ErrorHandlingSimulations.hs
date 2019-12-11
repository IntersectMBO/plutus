{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module ErrorHandlingSimulations where

import           ErrorHandling         (registeredKnownCurrencies)
import           Playground.Types      (Simulation (Simulation), SimulatorAction, simulationActions, simulationName,
                                        simulationWallets)
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
            , simulationWallets
            , simulationActions = [throwError wallet1, catchError wallet2]
            }

throwError :: Wallet -> SimulatorAction
throwError caller = callEndpoint caller "throwError" ()

catchError :: Wallet -> SimulatorAction
catchError caller = callEndpoint caller "catchError" ()
