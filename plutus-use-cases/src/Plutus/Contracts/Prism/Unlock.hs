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
-- | Two sample that unlock some funds by presenting the credentials.
--   * 'subscribeSTO' uses the credential to participate in an STO
--   * 'unlockExchange' uses the credential to take ownership of funds that
--     were locked by an exchange.
module Plutus.Contracts.Prism.Unlock(
    -- * STO
    STOSubscriber(..)
    , STOSubscriberSchema
    , subscribeSTO
    -- * Exchange
    , UnlockExchangeSchema
    , unlockExchange
    -- * Errors etc.
    , UnlockError(..)
    ) where

import           Data.Aeson                               (FromJSON, ToJSON)
import           GHC.Generics                             (Generic)
import           Ledger                                   (pubKeyHash, txId)
import qualified Ledger.Ada                               as Ada
import           Ledger.Constraints                       (SomeLookupsAndConstraints (..))
import qualified Ledger.Constraints                       as Constraints
import           Ledger.Crypto                            (PubKeyHash)
import           Ledger.Value                             (TokenName)
import           Plutus.Contract
import           Plutus.Contract.Effects.RPC              (HasRPCClient, RPCCallError, RPCClient, RPCResponse,
                                                           Retries (..), callRPC)
import           Plutus.Contracts.Prism.Credential        (Credential)
import qualified Plutus.Contracts.Prism.Credential        as Credential
import           Plutus.Contracts.Prism.CredentialManager (CredentialManager, CredentialManagerClientError)
import           Plutus.Contracts.Prism.STO               (STOData (..))
import qualified Plutus.Contracts.Prism.STO               as STO
import           Plutus.Contracts.Prism.StateMachine      (UserCredential (..))
import           Plutus.Contracts.TokenAccount            (TokenAccountError)
import qualified Plutus.Contracts.TokenAccount            as TokenAccount
import           Prelude                                  as Haskell
import           Schema                                   (ToSchema)

data STOSubscriber =
    STOSubscriber
        { wCredential   :: Credential
        , wSTOIssuer    :: PubKeyHash
        , wSTOTokenName :: TokenName
        , wSTOAmount    :: Integer
        }
    deriving stock (Generic, Haskell.Eq, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON, ToSchema)

type STOSubscriberSchema =
    BlockchainActions
        .\/ Endpoint "sto" STOSubscriber
        .\/ Endpoint "credential manager" ContractInstanceId
        .\/ RPCClient CredentialManager

-- | Obtain a token from the credential manager app,
--   then participate in the STO
subscribeSTO :: forall w s.
    ( HasBlockchainActions s
    , HasRPCClient CredentialManager s
    , HasEndpoint "sto" STOSubscriber s
    , HasEndpoint "credential manager" ContractInstanceId s
    )
    => Contract w s UnlockError ()
subscribeSTO = do
    STOSubscriber{wCredential, wSTOIssuer, wSTOTokenName, wSTOAmount} <-
        mapError WithdrawEndpointError
        $ endpoint @"sto"
    (credConstraints, credLookups) <- obtainCredentialTokenData wCredential
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

type UnlockExchangeSchema =
    BlockchainActions
        .\/ Endpoint "unlock from exchange" Credential
        .\/ Endpoint "credential manager" ContractInstanceId
        .\/ RPCClient CredentialManager

-- | Obtain a token from the credential manager app,
--   then use it to unlock funds that were locked by an exchange.
unlockExchange :: forall w s.
    ( HasBlockchainActions s
    , HasRPCClient CredentialManager s
    , HasEndpoint "unlock from exchange" Credential s
    , HasEndpoint "credential manager" ContractInstanceId s
    )
    => Contract w s UnlockError ()
unlockExchange = do
    credential <-
        mapError WithdrawEndpointError
        $ endpoint @"unlock from exchange"
    ownPK <- mapError WithdrawPkError $ pubKeyHash <$> ownPubKey
    (credConstraints, credLookups) <- obtainCredentialTokenData credential
    (accConstraints, accLookups) <-
        mapError UnlockExchangeTokenAccError
        $ TokenAccount.redeemTx (Credential.tokenAccount credential) ownPK
    case Constraints.mkSomeTx [SomeLookupsAndConstraints credLookups credConstraints, SomeLookupsAndConstraints accLookups accConstraints] of
        Left mkTxErr -> throwError (UnlockMkTxError mkTxErr)
        Right utx -> mapError WithdrawTxError $ do
            tx <- submitUnbalancedTx utx
            awaitTxConfirmed (txId tx)

-- | Get the constraints and script lookups that are needed to construct a
--   transaction that presents the 'Credential'
obtainCredentialTokenData :: forall w s.
    ( HasBlockchainActions s
    , HasRPCClient CredentialManager s
    , HasEndpoint "credential manager" ContractInstanceId s
    )
    => Credential
    -> Contract w s UnlockError (RPCResponse CredentialManager)
obtainCredentialTokenData credential = do
    credentialManager <- mapError WithdrawEndpointError $ endpoint @"credential manager"
    userCredential <- mapError WithdrawPkError $
        UserCredential
            <$> (pubKeyHash <$> ownPubKey)
            <*> pure credential
            <*> pure (Credential.token credential)
    rpcResult <-
        mapError TokenManagerRPCError
        $ callRPC @CredentialManager (MaxRetries 5) credentialManager userCredential
    case rpcResult of
        Left err -> throwError (CredentialManagerError err)
        Right p  -> pure p


---
-- logs / error
---

data UnlockError =
    WithdrawEndpointError ContractError
    | TokenManagerRPCError RPCCallError
    | TokenManagerAwaitError ContractError
    | WithdrawTxError ContractError
    | WithdrawPkError ContractError
    | CredentialManagerError CredentialManagerClientError
    | UnlockExchangeTokenAccError TokenAccountError
    | UnlockMkTxError Constraints.MkTxError
    deriving stock (Generic, Haskell.Eq, Haskell.Show)
    deriving anyclass (ToJSON, FromJSON)
