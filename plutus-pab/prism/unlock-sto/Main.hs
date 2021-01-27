{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
module Main where

import           Data.Bifunctor                                                   (first)
import           Data.Proxy                                                       (Proxy (..))
import           Language.Plutus.Contract                                         (BlockchainActions, type (.\/))
import           Language.Plutus.Contract.Effects.RPC                             (RPCClient)
import           Language.PlutusTx.Coordination.Contracts.Prism.CredentialManager (CredentialManager)
import           Language.PlutusTx.Coordination.Contracts.Prism.Unlock            as Prism
import           Plutus.PAB.ContractCLI                                           (commandLineApp')
import           Plutus.PAB.Utils                                                 (tshow)

main :: IO ()
main =
    commandLineApp'
        (Proxy @(BlockchainActions .\/ RPCClient CredentialManager))
        $ first tshow
        $ Prism.subscribeSTO @Prism.STOSubscriberSchema
