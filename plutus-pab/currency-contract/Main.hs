module Main
    ( main
    ) where

import           Control.Monad                                     (void)
import           Data.Bifunctor                                    (first)
import qualified Data.Text                                         as T
import           Language.PlutusTx.Coordination.Contracts.Currency (forgeCurrency)
import           Plutus.PAB.ContractCLI                            (commandLineApp)

main :: IO ()
main = commandLineApp $ first (T.pack . show) $ void forgeCurrency
