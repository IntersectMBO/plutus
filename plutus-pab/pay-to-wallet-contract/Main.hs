module Main
    ( main
    ) where

import           Data.Bifunctor                              (first)
import qualified Data.Text                                   as T
import           Plutus.PAB.ContractCLI                      (commandLineApp)
import           Plutus.PAB.Effects.ContractTest.PayToWallet (payToWallet)

main :: IO ()
main = commandLineApp $ first (T.pack . show) payToWallet
