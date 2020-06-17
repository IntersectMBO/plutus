module Main
    ( main
    ) where

import           Control.Monad                                     (void)
import           Data.Bifunctor                                    (first)
import           Language.PlutusTx.Coordination.Contracts.Currency (forgeCurrency)
import           Plutus.SCB.ContractCLI                            (commandLineApp)
import           Plutus.SCB.Utils                                  (tshow)

main :: IO ()
main = commandLineApp $ first tshow $ void forgeCurrency
