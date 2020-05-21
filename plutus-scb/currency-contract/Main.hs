module Main
    ( main
    ) where

import           Control.Monad                                     (void)
import           Language.PlutusTx.Coordination.Contracts.Currency (forgeCurrency)
import           Plutus.SCB.ContractCLI                            (commandLineApp)

main :: IO ()
main = commandLineApp $ void forgeCurrency
