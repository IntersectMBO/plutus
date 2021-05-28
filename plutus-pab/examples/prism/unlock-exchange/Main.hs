{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Main where

import           Data.Bifunctor                           (first)
import           Data.Proxy                               (Proxy (..))
import           Data.Text.Extras                         (tshow)
import           Plutus.Contract                          (BlockchainActions, type (.\/))
import           Plutus.Contract.Effects.RPC              (RPCClient)
import           Plutus.Contracts.Prism.CredentialManager (CredentialManager)
import           Plutus.Contracts.Prism.Unlock            as Prism
import           Plutus.PAB.ContractCLI                   (commandLineApp')

main :: IO ()
main =
    commandLineApp'
        (Proxy @(BlockchainActions .\/ RPCClient CredentialManager))
        $ first tshow
        $ Prism.unlockExchange @() @Prism.UnlockExchangeSchema
