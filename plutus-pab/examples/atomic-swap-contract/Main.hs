module Main
    ( main
    ) where

import           AtomicSwap             (atomicSwap)
import           Data.Bifunctor         (first)
import qualified Data.Text              as T
import           Plutus.PAB.ContractCLI (commandLineApp)

main :: IO ()
main = commandLineApp $ first (T.pack . show) atomicSwap
