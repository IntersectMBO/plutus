module Main
    ( main
    ) where

import           Data.Bifunctor                              (first)
import           Plutus.PAB.ContractCLI                      (commandLineApp)
import           Plutus.PAB.Effects.ContractTest.PayToWallet (payToWallet)
import           Plutus.PAB.Utils                            (tshow)

main :: IO ()
main = commandLineApp $ first tshow payToWallet
