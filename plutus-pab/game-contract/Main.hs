module Main
    ( main
    ) where

import           Plutus.Contracts.Game  (game)
import           Plutus.PAB.ContractCLI (commandLineApp)

main :: IO ()
main = commandLineApp game
