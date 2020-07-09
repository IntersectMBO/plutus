module Main
    ( main
    ) where

import           Data.Bifunctor                              (first)
import           Plutus.SCB.ContractCLI                      (commandLineApp)
import           Plutus.SCB.Effects.ContractTest.PayToWallet (payToWallet)
import           Plutus.SCB.Utils                            (tshow)

main :: IO ()
main = commandLineApp $ first tshow payToWallet
