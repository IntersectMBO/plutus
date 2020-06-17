{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.OwnPubKey where

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras
import           GHC.Generics                     (Generic)
import           Ledger.Crypto                    (PubKey)

import           Language.Plutus.Contract.Request (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract)

type OwnPubKeySym = "own-pubkey"

type HasOwnPubKey s =
  ( HasType OwnPubKeySym PubKey (Input s)
  , HasType OwnPubKeySym OwnPubKeyRequest (Output s)
  , ContractRow s)

type OwnPubKey = OwnPubKeySym .== (PubKey, OwnPubKeyRequest)

data OwnPubKeyRequest = WaitingForPubKey
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)

deriving via (PrettyShow OwnPubKeyRequest) instance Pretty OwnPubKeyRequest

-- | Get a public key belonging to the wallet that runs this contract.
--   * Any funds paid to this public key will be treated as the wallet's own
--     funds
--   * The wallet is able to sign transactions with the private key of this
--     public key, for example, if the public key is added to the
--     'requiredSignatures' field of 'Tx'.
--   * There is a 1-n relationship between wallets and public keys (although in
--     the mockchain n=1)
ownPubKey :: forall s e. (AsContractError e, HasOwnPubKey s) => Contract s e PubKey
ownPubKey = requestMaybe @OwnPubKeySym @_ @_ @s WaitingForPubKey Just

event
    :: forall s.
    ( HasOwnPubKey s )
    => PubKey
    -> Event s
event = Event . IsJust (Label @OwnPubKeySym)

request
    :: forall s.
    ( HasOwnPubKey s )
    => Handlers s
    -> Maybe OwnPubKeyRequest
request (Handlers r) = trial' r (Label @OwnPubKeySym)
