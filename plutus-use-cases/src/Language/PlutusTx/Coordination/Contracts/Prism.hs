{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}

module Language.PlutusTx.Coordination.Contracts.Prism(
    -- $prism
    -- * Withdraw app
    Withdrawal(..)
    , WithdrawSchema
    , WithdrawError(..)
    , withdraw
    -- * Mirror app
    , MirrorSchema
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
import           Language.PlutusTx.Coordination.Contracts.Prism.Withdraw

import           Language.Plutus.Contract

-- $prism
-- This module and its submodules define the Plutus part of a credential
-- management dapp such as Atala PRISM / Mirror.
--
-- There are two actors:
--
-- * Mirror. Issues and revokes the on-chain credential tokens.
-- * User. Uses credentials in transactions
--
-- We have the following modules.
--
-- 1. .Credential: Defines the 'Credential' type and a monetary policy script
--    (MPS) for creating and destroying credential tokens
-- 2. .StateMachine: Defines the state machine script that allows Users to
--    present their credentials in transactions and Mirror to revoke/destroy
--    credentials.
-- 3. .STO: A simple Security Token Offering (STO) that requires a credential
--    to be presented by anyone who wants to participate. This is provided for
--    testing and demo purposes
-- 4. .CredentialManager: A Plutus application managing all the credentials
--    that are available to the User.
-- 5. .Mirror: A Plutus application that locks credentials in state machines
--    and revokes them when necessary.
-- 6. .Withdraw: A Plutus application that asks the 'CredentialManager' app for
--    credentials and then participates in the STO.


data Role = CredMan | Mirror | Withdraw
    deriving stock (Eq, Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

type PrismSchema =
    CredentialManagerSchema
    .\/ MirrorSchema
    .\/ WithdrawSchema
    .\/ Endpoint "role" Role

data PrismError =
    WithdrawErr WithdrawError
    | MirrorErr MirrorError
    | CredManErr CredentialManagerError
    | EPError ContractError
    deriving stock (Eq, Generic, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | A wrapper around the three prism contracts (used in the emulator where
--   we can only deploy a single contract)
contract ::
    Contract PrismSchema PrismError ()
contract = do
    r <- mapError EPError $ endpoint @"role"
    case r of
        CredMan  -> mapError CredManErr credentialManager
        Mirror   -> mapError MirrorErr mirror
        Withdraw -> mapError WithdrawErr withdraw
