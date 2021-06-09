{-# LANGUAGE TypeApplications #-}
module Main where

import           Data.Bifunctor                (first)
import           Data.Proxy                    (Proxy (..))
import           Data.Text.Extras              (tshow)
import           Plutus.Contract               (EmptySchema)
import           Plutus.Contracts.Prism.Unlock as Prism
import           Plutus.PAB.ContractCLI        (commandLineApp')

main :: IO ()
main =
    commandLineApp'
        (Proxy @EmptySchema)
        $ first tshow
        $ Prism.unlockExchange @() @Prism.UnlockExchangeSchema
