{-# LANGUAGE TypeApplications #-}
module Main where

import           Data.Bifunctor                (first)
import           Data.Proxy                    (Proxy (..))
import           Data.Text.Extras              (tshow)
import           Plutus.Contract               (BlockchainActions)
import           Plutus.Contracts.Prism.Unlock as Prism
import           Plutus.PAB.ContractCLI        (commandLineApp')

main :: IO ()
main =
    commandLineApp'
        (Proxy @BlockchainActions)
        $ first tshow
        $ Prism.unlockExchange @() @Prism.UnlockExchangeSchema
