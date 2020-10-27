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
module Language.PlutusTx.Coordination.Contracts.Prism.Mirror(
    MirrorSchema
    , CredentialOwnerReference(..)
    , MirrorError(..)
    , mirror
    ) where

import           Control.Monad                                               (void)
import           Control.Monad                                               (forever)
import           Data.Aeson                                                  (FromJSON, ToJSON)
import           GHC.Generics                                                (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.StateMachine                       (SMContractError, runInitialise, runStep)
import           Language.PlutusTx.Coordination.Contracts.Prism.Credential   (Credential (..), CredentialAuthority (..))
import qualified Language.PlutusTx.Coordination.Contracts.Prism.Credential   as Credential
import           Language.PlutusTx.Coordination.Contracts.Prism.StateMachine as StateMachine
import           Ledger                                                      (txId)
import qualified Ledger.Constraints                                          as Constraints
import           Ledger.Crypto                                               (PubKeyHash, pubKeyHash)
import qualified Ledger.Typed.Scripts                                        as Scripts
import           Ledger.Value                                                (TokenName)
import           Schema                                                      (ToSchema)
import           Wallet.Emulator                                             (walletPubKey)
import           Wallet.Emulator.Wallet                                      (Wallet)

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
    => Contract s MirrorError ()
mirror = do
    authority <- mapError SetupError $ CredentialAuthority . pubKeyHash <$> ownPubKey
    forever $ (createTokens authority `select` revokeToken authority)

createTokens ::
    ( HasEndpoint "issue" CredentialOwnerReference s
    , HasBlockchainActions s
    )
    => CredentialAuthority
    -> Contract s MirrorError ()
createTokens authority = do
    CredentialOwnerReference{coTokenName, coOwner} <- mapError IssueEndpointError $ endpoint @"issue"
    let lookups = Constraints.monetaryPolicy (Credential.policy authority)
        theToken = Credential.token Credential{credAuthority=authority,credName=coTokenName}
        constraints =
            Constraints.mustForgeValue theToken
            <> Constraints.mustBeSignedBy (Credential.unCredentialAuthority authority)
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
    -> Contract s MirrorError ()
revokeToken authority = do
    CredentialOwnerReference{coTokenName, coOwner} <- mapError RevokeEndpointError $ endpoint @"revoke"
    let stateMachine = StateMachine.mkMachineClient authority (pubKeyHash $ walletPubKey coOwner) coTokenName
    void $ mapError StateMachineError $ runStep stateMachine RevokeCredential

---
-- Errors and Logging
---

data MirrorError =
    StateNotFound TokenName PubKeyHash
    | SetupError ContractError
    | IssueEndpointError ContractError
    | RevokeEndpointError ContractError
    | CreateTokenTxError ContractError
    | StateMachineError (SMContractError IDState IDAction)
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)
