{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Main where

import           Data.Bifunctor                                                   (first)
import           Data.Proxy                                                       (Proxy (..))
import           Language.Plutus.Contract                                         (BlockchainActions, type (.\/))
import           Language.Plutus.Contract.Effects.RPC                             (RPCServer)
import           Language.PlutusTx.Coordination.Contracts.Prism.CredentialManager (CredentialManager,
                                                                                   CredentialManagerSchema,
                                                                                   credentialManager)
import           Plutus.SCB.ContractCLI                                           (commandLineApp')
import           Plutus.SCB.Utils                                                 (tshow)

main :: IO ()
main =
    commandLineApp'
        (Proxy @(BlockchainActions .\/ RPCServer CredentialManager))
        $ first tshow
        $ credentialManager @CredentialManagerSchema
