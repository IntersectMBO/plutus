{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module HelloWorldSimulations where

import           HelloWorld            (registeredKnownCurrencies)
import           Playground.Types      (ContractCall (AddBlocks), Simulation (Simulation), simulationActions,
                                        simulationName, simulationWallets)
import           SimulationUtils       (simulatorWallet)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [helloWorld]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100 <$>
        [wallet1, wallet2]
    helloWorld =
        Simulation
            { simulationName = "Hello, world"
            , simulationWallets
            , simulationActions = [ AddBlocks 1 ]
            }
