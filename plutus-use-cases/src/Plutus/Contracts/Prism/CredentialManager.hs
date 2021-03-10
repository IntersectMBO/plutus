{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE MonoLocalBinds     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
-- | The credential tokens application. Runs on the user's machine.
module Language.PlutusTx.Coordination.Contracts.Prism.CredentialManager(
    CredentialManager
    , CredentialManagerSchema
    , CredentialManagerClientError(..)
    , CredentialManagerError(..)
    , credentialManager
    ) where

import           Data.Aeson                                                  (FromJSON, ToJSON)
import           GHC.Generics                                                (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects.RPC
import           Language.Plutus.Contract.StateMachine                       (InvalidTransition, SMContractError,
                                                                              StateMachine, StateMachineTransition (..),
                                                                              mkStep)
import           Language.PlutusTx.Coordination.Contracts.Prism.StateMachine (IDAction (PresentCredential), IDState,
                                                                              UserCredential (..))
import qualified Language.PlutusTx.Coordination.Contracts.Prism.StateMachine as StateMachine
import           Language.PlutusTx.Prelude
import           Ledger.Constraints                                          (ScriptLookups, TxConstraints (..))
import qualified Prelude                                                     as Haskell

data CredentialManager

instance RPC CredentialManager where
    type RPCRequest CredentialManager = UserCredential
    type RPCRequestEndpoint CredentialManager = "credential-token-req"
    type RPCResponse CredentialManager = (TxConstraints IDAction IDState, ScriptLookups (StateMachine IDState IDAction))
    type RPCResponseEndpoint CredentialManager = "credential-token-resp"
    type RPCError CredentialManager = CredentialManagerClientError

type CredentialManagerSchema =
    BlockchainActions
        .\/ RPCServer CredentialManager

-- | The Plutus application that keeps track of user credentials.
credentialManager :: forall w s.
    ( HasBlockchainActions s
    , HasRPCServer CredentialManager s
    )
    => Contract w s CredentialManagerError ()
credentialManager =
    let go = do
            mapError TokenAppServerRPCError (respondRPC @w @CredentialManager @s presentToken)
            go
    in go

-- | Error that occurs when running the 'credential-token-req' RPC call.
--   This needs to be handled by the client.
data CredentialManagerClientError =
    StateMachineError SMContractError
    | TransitionError (InvalidTransition IDState IDAction)
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data CredentialManagerError =
    TokenAppServerContractError ContractError
    | TokenAppServerRPCError RPCRespondError
    deriving stock (Show, Haskell.Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Server side implementation of the 'CredentialManager' RPC. This simply calls the 'PresentCredential'
--   step on the state machine instance and returns the constraints needed to construct a transaction
--   that presents the token.
presentToken :: forall w s.
    ( HasBlockchainActions s
    )
    => UserCredential
    -> Contract w s CredentialManagerClientError (TxConstraints IDAction IDState, ScriptLookups (StateMachine IDState IDAction))
presentToken userCredential = do
    let theClient = StateMachine.machineClient (StateMachine.scriptInstance userCredential) userCredential
    t <- mapError StateMachineError $ mkStep theClient PresentCredential
    case t of
        Left e -> throwError (TransitionError e)
        Right StateMachineTransition{smtConstraints=cons, smtLookups=lookups} ->
            pure (cons, lookups)
