module Main
    ( main
    ) where

import           Data.Bifunctor                    (first)
import qualified Data.Text                         as T
import           Plutus.Contracts.GameStateMachine (contract)
import           Plutus.PAB.ContractCLI            (commandLineApp)

main :: IO ()
main = commandLineApp $ first (T.pack . show) contract
