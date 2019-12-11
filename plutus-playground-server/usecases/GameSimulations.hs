{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module GameSimulations where

import           Game                  (GuessParams (GuessParams), LockParams (LockParams), amount, guessWord,
                                        registeredKnownCurrencies, secretWord)
import qualified Ledger.Ada            as Ada
import           Playground.Types      (Simulation (Simulation), SimulatorAction, simulationActions, simulationName,
                                        simulationWallets)
import           SimulationUtils       (callEndpoint, simulatorWallet)
import           Wallet.Emulator.Types (Wallet (Wallet), getWallet)

simulations :: [Simulation]
simulations = [basicGame, badGuess]
  where
    wallet1 = Wallet {getWallet = 1}
    wallet2 = Wallet {getWallet = 2}
    wallet3 = Wallet {getWallet = 3}
    simulationWallets =
        simulatorWallet registeredKnownCurrencies 100 <$>
        [wallet1, wallet2, wallet3]
    basicGame =
        Simulation
            { simulationName = "Basic Game"
            , simulationWallets
            , simulationActions =
                  [lock wallet1 "Plutus" 50, guess wallet2 "Plutus"]
            }
    badGuess =
        Simulation
            { simulationName = "One Bad Guess"
            , simulationWallets
            , simulationActions =
                  [ lock wallet1 "Plutus" 50
                  , guess wallet2 "Marlowe"
                  , guess wallet3 "Plutus"
                  ]
            }

lock :: Wallet -> String -> Integer -> SimulatorAction
lock caller secretWord balance =
    callEndpoint
        caller
        "lock"
        LockParams {secretWord, amount = Ada.lovelaceOf balance}

guess :: Wallet -> String -> SimulatorAction
guess caller guessWord = callEndpoint caller "guess" (GuessParams {guessWord})
