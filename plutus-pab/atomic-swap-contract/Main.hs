module Main
    ( main
    ) where

import           Data.Bifunctor                             (first)
import           Plutus.PAB.ContractCLI                     (commandLineApp)
import           Plutus.PAB.Effects.ContractTest.AtomicSwap (atomicSwap)
import           Plutus.PAB.Utils                           (tshow)

main :: IO ()
main = commandLineApp $ first tshow atomicSwap
