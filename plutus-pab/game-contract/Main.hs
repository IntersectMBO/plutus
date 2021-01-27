module Main
    ( main
    ) where

import           Language.PlutusTx.Coordination.Contracts.Game (game)
import           Plutus.PAB.ContractCLI                        (commandLineApp)

main :: IO ()
main = commandLineApp game
