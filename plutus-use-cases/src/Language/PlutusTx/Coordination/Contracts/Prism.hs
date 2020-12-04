{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}

{-
This module and its submodules define the Plutus part of a credential
management dapp such as Atala PRISM / Mirror.

There are two actors:

* Mirror. Issues and revokes the on-chain credential tokens.
* User. Uses credentials in transactions

We have the following modules.

1. .Credential: Defines the 'Credential' type and a forging policy script
   for creating and destroying credential tokens
2. .StateMachine: Defines the state machine script that allows Users to
   present their credentials in transactions and Mirror to revoke/destroy
   credentials.
3. .STO: A simple Security Token Offering (STO) that requires a credential
   to be presented by anyone who wants to participate. This is provided for
   testing and demo purposes
4. .CredentialManager: A Plutus application managing all the credentials
   that are available to the User.
5. .Mirror: A Plutus application that locks credentials in state machines
   and revokes them when necessary.
6. .Unlock: Two Plutus applications that each present a credential to unlock
   some funds.

We work with two different script hashes: The hash of the monetary policy that
forges the tokens (see 'policy'), and the hash of the state machine instance
that locks a specific credential token for a specific user, identified by their
public key address.

-}
module Language.PlutusTx.Coordination.Contracts.Prism(
    -- * Unlock (STO)
    STOSubscriber(..)
    , STOSubscriberSchema
    , UnlockError(..)
    , subscribeSTO
    -- * Unlock (exchange)
    , UnlockExchangeSchema
    , unlockExchange
    -- * Mirror app
    , MirrorSchema
    , CredentialOwnerReference(..)
    , MirrorError(..)
    , mirror
    -- * Credential manager app
    , Credential(..)
    , UserCredential(..)
    , CredentialAuthority(..)
    , CredentialManagerSchema
    , CredentialManagerError(..)
    , credentialManager
    -- * all-in-one
    , Role(..)
    , PrismSchema
    , PrismError(..)
    , contract
    ) where

import           Data.Aeson                                                       (FromJSON, ToJSON)
import           GHC.Generics                                                     (Generic)
import           Language.PlutusTx.Coordination.Contracts.Prism.Credential
import           Language.PlutusTx.Coordination.Contracts.Prism.CredentialManager
import           Language.PlutusTx.Coordination.Contracts.Prism.Mirror
import           Language.PlutusTx.Coordination.Contracts.Prism.StateMachine
import           Language.PlutusTx.Coordination.Contracts.Prism.Unlock

import           Language.Plutus.Contract

-- | The roles that we pass to 'contract'.
data Role
    = CredMan -- ^ The 'credentialManager' contract
    | Mirror -- ^ The 'mirror' contract
    | UnlockSTO -- ^ The 'subscribeSTO' contract
    | UnlockExchange -- ^ The 'unlockExchange' contract
    deriving stock (Eq, Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

type PrismSchema =
    CredentialManagerSchema
    .\/ MirrorSchema
    .\/ STOSubscriberSchema
    .\/ UnlockExchangeSchema
    .\/ Endpoint "role" Role

{- With the implementation of .\/ from row-types, GHC chokes on the above type because of the four
   repeated BlockchainActions. Using our own implementation from Data.Row.Extras everything is fine. -}

data PrismError =
    UnlockSTOErr UnlockError
    | MirrorErr MirrorError
    | CredManErr CredentialManagerError
    | EPError ContractError
    | UnlockExchangeErr UnlockError
    deriving stock (Eq, Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | A wrapper around the four prism contracts. This is just a workaround
--   for the emulator, where we can only ever run a single 'Contract'. In
--   the SCB we could simply start all four contracts (credentialManager,
--   mirror, subscribeSTO, subscribeExchange) separately.
contract ::
    Contract PrismSchema PrismError ()
contract = do
    r <- mapError EPError $ endpoint @"role"
    case r of
        CredMan        -> mapError CredManErr credentialManager
        Mirror         -> mapError MirrorErr mirror
        UnlockSTO      -> mapError UnlockSTOErr subscribeSTO
        UnlockExchange -> mapError UnlockExchangeErr unlockExchange
