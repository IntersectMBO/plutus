{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}

module GameSimulations where

import           Game                  (GuessParams (GuessParams), LockParams (LockParams), amount, guessWord,
                                        registeredKnownCurrencies, secretWord)
import qualified Ledger.Ada            as Ada
import           Playground.Types      (ContractCall (AddBlocks), Simulation (Simulation), SimulatorAction,
                                        simulationActions, simulationIndex, simulationName, simulationWallets)
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
            , simulationIndex = 1
            , simulationWallets
            , simulationActions =
                  [ lock wallet1 "Plutus" 50
                  , AddBlocks 1
                  , guess wallet2 "Plutus"
                  , AddBlocks 1
                  ]
            }
    badGuess =
        Simulation
            { simulationName = "One Bad Guess"
            , simulationIndex = 2
            , simulationWallets
            , simulationActions =
                  [ lock wallet1 "Plutus" 50
                  , AddBlocks 1
                  , guess wallet2 "Marlowe"
                  , AddBlocks 1
                  , guess wallet3 "Plutus"
                  , AddBlocks 1
                  ]
            }

lock :: Wallet -> String -> Integer -> SimulatorAction
lock caller secretWord balance =
    callEndpoint
        caller
        "lock"
        LockParams {secretWord, amount = Ada.lovelaceValueOf balance}

guess :: Wallet -> String -> SimulatorAction
guess caller guessWord = callEndpoint caller "guess" (GuessParams {guessWord})
