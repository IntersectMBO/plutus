{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module StarterSimulations where

import           Ledger.Ada            (lovelaceValueOf)
import           Ledger.Value          (Value)
import           Playground.Types      (ContractCall (PayToWallet), Simulation (Simulation), SimulatorAction, amount,
                                        recipient, sender, simulationActions, simulationName, simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Starter               (registeredKnownCurrencies)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [publishRedeem, payToWallet]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100 <$> [wallet1, wallet2]
    publishRedeem =
        Simulation
            { simulationName = "Publish/Redeem"
            , simulationWallets
            , simulationActions =
                  [ publish wallet1 (12345, lovelaceValueOf 20)
                  , redeem wallet2 12345
                  ]
            }
    payToWallet =
        Simulation
            { simulationName = "Pay To Wallet"
            , simulationWallets
            , simulationActions =
                  [ PayToWallet
                        { sender = wallet1
                        , recipient = wallet2
                        , amount = lovelaceValueOf 24
                        }
                  ]
            }

publish :: Wallet -> (Integer, Value) -> SimulatorAction
publish caller = callEndpoint caller "publish"

redeem :: Wallet -> Integer -> SimulatorAction
redeem caller = callEndpoint caller "redeem"
