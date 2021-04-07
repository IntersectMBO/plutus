{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
-- | The Atala Mirror application that initialises the state machine
module Plutus.Contracts.Prism.Mirror(
    MirrorSchema
    , CredentialOwnerReference(..)
    , MirrorError(..)
    , mirror
    ) where

import           Control.Lens
import           Control.Monad                       (forever, void)
import           Data.Aeson                          (FromJSON, ToJSON)
import           GHC.Generics                        (Generic)
import           Ledger                              (txId)
import qualified Ledger.Ada                          as Ada
import qualified Ledger.Constraints                  as Constraints
import           Ledger.Crypto                       (PubKeyHash, pubKeyHash)
import qualified Ledger.Typed.Scripts                as Scripts
import           Ledger.Value                        (TokenName)
import           Plutus.Contract
import           Plutus.Contract.StateMachine        (AsSMContractError (..), SMContractError,
                                                      StateMachineTransition (..), mkStep, runInitialise)
import           Plutus.Contracts.Prism.Credential   (Credential (..), CredentialAuthority (..))
import qualified Plutus.Contracts.Prism.Credential   as Credential
import           Plutus.Contracts.Prism.StateMachine as StateMachine
import           Schema                              (ToSchema)
import           Wallet.Emulator                     (walletPubKey)
import           Wallet.Emulator.Wallet              (Wallet)

-- | Reference to a credential tied to a specific owner (public key address).
--   From this, and the public key of the Mirror instance, we can compute the
--   address of the state machine script that locks the token for the owner.
data CredentialOwnerReference =
    CredentialOwnerReference
        { coTokenName :: TokenName
        , coOwner     :: Wallet
        }
    deriving stock (Generic, Eq, Show, Ord)
    deriving anyclass (ToJSON, FromJSON, ToSchema)

type MirrorSchema =
    BlockchainActions
        .\/ Endpoint "issue" CredentialOwnerReference -- lock a single credential token in a state machine tied to the credential token owner
        .\/ Endpoint "revoke" CredentialOwnerReference -- revoke a credential token token from its owner by calling 'Revoke' on the state machine instance

mirror ::
    ( HasBlockchainActions s
    , HasEndpoint "revoke" CredentialOwnerReference s
    , HasEndpoint "issue" CredentialOwnerReference s
    )
    => Contract w s MirrorError ()
mirror = do
    authority <- mapError SetupError $ CredentialAuthority . pubKeyHash <$> ownPubKey
    forever $ (createTokens authority `select` revokeToken authority)

createTokens ::
    ( HasEndpoint "issue" CredentialOwnerReference s
    , HasBlockchainActions s
    )
    => CredentialAuthority
    -> Contract w s MirrorError ()
createTokens authority = do
    CredentialOwnerReference{coTokenName, coOwner} <- mapError IssueEndpointError $ endpoint @"issue"
    let pk      = Credential.unCredentialAuthority authority
        lookups = Constraints.monetaryPolicy (Credential.policy authority)
                  <> Constraints.ownPubKeyHash pk
        theToken = Credential.token Credential{credAuthority=authority,credName=coTokenName}
        constraints =
            Constraints.mustForgeValue theToken
            <> Constraints.mustBeSignedBy pk
            <> Constraints.mustPayToPubKey pk (Ada.lovelaceValueOf 1)   -- Add self-spend to force an input
    _ <- mapError CreateTokenTxError $ do
            tx <- submitTxConstraintsWith @Scripts.Any lookups constraints
            awaitTxConfirmed (txId tx)
    let stateMachine = StateMachine.mkMachineClient authority (pubKeyHash $ walletPubKey coOwner) coTokenName
    void $ mapError StateMachineError $ runInitialise stateMachine Active theToken

revokeToken ::
    ( HasBlockchainActions s
    , HasEndpoint "revoke" CredentialOwnerReference s
    )
    => CredentialAuthority
    -> Contract w s MirrorError ()
revokeToken authority = do
    CredentialOwnerReference{coTokenName, coOwner} <- mapError RevokeEndpointError $ endpoint @"revoke"
    let stateMachine = StateMachine.mkMachineClient authority (pubKeyHash $ walletPubKey coOwner) coTokenName
        lookups = Constraints.monetaryPolicy (Credential.policy authority) <>
                  Constraints.ownPubKeyHash  (Credential.unCredentialAuthority authority)
    t <- mapError StateMachineError $ mkStep stateMachine RevokeCredential
    case t of
        Left{} -> return () -- Ignore invalid transitions
        Right StateMachineTransition{smtConstraints=constraints, smtLookups=lookups'} -> do
            tx <- submitTxConstraintsWith (lookups <> lookups') constraints
            awaitTxConfirmed (txId tx)

---
-- Errors and Logging
---

data MirrorError =
    StateNotFound TokenName PubKeyHash
    | SetupError ContractError
    | IssueEndpointError ContractError
    | RevokeEndpointError ContractError
    | CreateTokenTxError ContractError
    | StateMachineError SMContractError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''MirrorError

instance AsSMContractError MirrorError where
    _SMContractError = _StateMachineError

instance AsContractError MirrorError where
    _ContractError =  _SMContractError . _ContractError

