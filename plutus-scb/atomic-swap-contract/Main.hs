module Main
    ( main
    ) where

import           Data.Bifunctor                             (first)
import           Plutus.SCB.ContractCLI                     (commandLineApp)
import           Plutus.SCB.Effects.ContractTest.AtomicSwap (atomicSwap)
import           Plutus.SCB.Utils                           (tshow)

main :: IO ()
main = commandLineApp $ first tshow atomicSwap
