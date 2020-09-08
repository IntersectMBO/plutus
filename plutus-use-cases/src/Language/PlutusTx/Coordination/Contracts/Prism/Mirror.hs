{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
-- | The Atala mirror application that initialises the state machine
module Language.PlutusTx.Coordination.Contracts.Prism.Mirror(
    MirrorSchema
    , MirrorError(..)
    , mirror
    ) where

import           Control.Monad                                               (void)
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

type MirrorSchema =
    BlockchainActions
        .\/ Endpoint "issue" (TokenName, PubKeyHash) -- lock a single token in a state machine tied to the client address
        .\/ Endpoint "revoke" (TokenName, PubKeyHash) -- revoke a token from a state machine

mirror ::
    ( HasBlockchainActions s
    , HasEndpoint "revoke" (TokenName, PubKeyHash) s
    , HasEndpoint "issue" (TokenName, PubKeyHash) s
    )
    => Contract s MirrorError ()
mirror = do
    authority <- mapError SetupError $ CredentialAuthority . pubKeyHash <$> ownPubKey
    let go = (createTokens authority `select` revokeToken authority) >> go
    go

createTokens ::
    ( HasEndpoint "issue" (TokenName, PubKeyHash) s
    , HasBlockchainActions s
    )
    => CredentialAuthority
    -> Contract s MirrorError ()
createTokens authority = do
    (tokenName, credentialOwner) <- mapError IssueEndpointError $ endpoint @"issue"
    let authorityPk = Credential.unCredentialAuthority authority
        policy = Credential.policy authority
        credential = Credential{credAuthority=authority,credName=tokenName}
        lookups = Constraints.monetaryPolicy policy
        theToken = Credential.token credential
        constraints =
            Constraints.mustForgeValue theToken
            <> Constraints.mustBeSignedBy authorityPk
    _ <- mapError CreateTokenTxError
            $ (submitTxConstraintsWith @Scripts.Any lookups constraints >>= awaitTxConfirmed . txId)
    let stateMachine = StateMachine.mkMachineClient authority credentialOwner tokenName
    void $ mapError StateMachineError $ runInitialise stateMachine Active theToken

revokeToken ::
    ( HasBlockchainActions s
    , HasEndpoint "revoke" (TokenName, PubKeyHash) s
    )
    => CredentialAuthority
    -> Contract s MirrorError ()
revokeToken authority = do
    (tokenName, credentialOwner) <- mapError RevokeEndpointError $ endpoint @"revoke"
    let stateMachine = StateMachine.mkMachineClient authority credentialOwner tokenName
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
