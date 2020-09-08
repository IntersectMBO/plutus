{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
-- | The withdrawal application that withdraws some funds
module Language.PlutusTx.Coordination.Contracts.Prism.Withdraw(
    Withdrawal(..)
    , WithdrawSchema
    , WithdrawError(..)
    , withdraw
    ) where

import           Data.Aeson                                                       (FromJSON, ToJSON)
import           GHC.Generics                                                     (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects.RPC                             (HasRPCClient, RPCCallError,
                                                                                   RPCClient, callRPC)
import           Language.PlutusTx.Coordination.Contracts.Prism.Credential        (Credential)
import qualified Language.PlutusTx.Coordination.Contracts.Prism.Credential        as Credential
import           Language.PlutusTx.Coordination.Contracts.Prism.CredentialManager (CredentialManager,
                                                                                   CredentialManagerClientError)
import           Language.PlutusTx.Coordination.Contracts.Prism.StateMachine      (UserCredential (..))
import           Language.PlutusTx.Coordination.Contracts.Prism.STO               (STOData (..))
import qualified Language.PlutusTx.Coordination.Contracts.Prism.STO               as STO
import           Ledger                                                           (pubKeyHash, txId)
import qualified Ledger.Ada                                                       as Ada
import qualified Ledger.Constraints                                               as Constraints
import           Ledger.Crypto                                                    (PubKeyHash)
import           Ledger.Value                                                     (TokenName)
import           Prelude                                                          as Haskell

data Withdrawal =
    Withdrawal
        { wCredential   :: Credential
        , wSTOIssuer    :: PubKeyHash
        , wSTOTokenName :: TokenName
        , wSTOAmount    :: Integer
        }
    deriving stock (Generic, Haskell.Eq, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)

type WithdrawSchema =
    BlockchainActions
        .\/ Endpoint "withdraw" Withdrawal
        .\/ Endpoint "credential manager" ContractInstanceId
        .\/ RPCClient CredentialManager

-- | Obtains a token from the credential manager app,
--   then participates in the STO
withdraw :: forall s.
    ( HasBlockchainActions s
    , HasRPCClient CredentialManager s
    , HasEndpoint "withdraw" Withdrawal s
    , HasEndpoint "credential manager" ContractInstanceId s
    )
    => Contract s WithdrawError ()
withdraw = do
    Withdrawal{wCredential, wSTOIssuer, wSTOTokenName, wSTOAmount} <-
        mapError WithdrawEndpointError
        $ endpoint @"withdraw"
    credentialManager <- mapError WithdrawEndpointError $ endpoint @"credential manager"
    userCredential <- mapError WithdrawPkError $
        UserCredential
            <$> (pubKeyHash <$> ownPubKey)
            <*> pure wCredential
            <*> pure (Credential.token wCredential)
    rpcResult <-
        mapError TokenManagerRPCError
        $ callRPC @CredentialManager credentialManager userCredential
    (credConstraints, credLookups) <- case rpcResult of
        Left err -> throwError (CredentialManagerError err)
        Right p  -> pure p
    let stoData =
            STOData
                { stoIssuer = wSTOIssuer
                , stoTokenName = wSTOTokenName
                , stoCredentialToken = Credential.token wCredential
                }
        stoCoins = STO.coins stoData wSTOAmount
        constraints =
            Constraints.mustForgeValue stoCoins
            <> Constraints.mustPayToPubKey wSTOIssuer (Ada.lovelaceValueOf wSTOAmount)
            <> credConstraints
        lookups =
            Constraints.monetaryPolicy (STO.policy stoData)
            <> credLookups
    mapError WithdrawTxError
        $ submitTxConstraintsWith lookups constraints >>= awaitTxConfirmed . txId

---
-- logs / error
---

data WithdrawError =
    WithdrawEndpointError ContractError
    | TokenManagerRPCError RPCCallError
    | WithdrawTxError ContractError
    | WithdrawPkError ContractError
    | CredentialManagerError CredentialManagerClientError
    deriving stock (Generic, Haskell.Eq, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)
