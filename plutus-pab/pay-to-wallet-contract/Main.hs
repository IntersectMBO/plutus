module Main
    ( main
    ) where

import           Data.Bifunctor         (first)
import qualified Data.Text              as T
import           PayToWallet            (payToWallet)
import           Plutus.PAB.ContractCLI (commandLineApp)

main :: IO ()
main = commandLineApp $ first (T.pack . show) payToWallet
