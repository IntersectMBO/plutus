{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Language.Plutus.Contract.Effects.OwnPubKey where

import           Data.Aeson                       (FromJSON, ToJSON, toJSON)
import qualified Data.Aeson                       as JSON
import           Data.Aeson.Types                 (withText)
import           Data.Row
import qualified Data.Text                        as Text
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

-- TODO Aeson encodes this single no-arg constructor as, '{ tag:
-- OwnPubKey, contents: [] }', which our PureScript decoders can't
-- handle.
-- The correct fix is on the PureScript side - because we consider
-- whatever Aeson does to be canon - but for now this is equivalent
-- and faster.
instance ToJSON OwnPubKeyRequest where
    toJSON WaitingForPubKey = JSON.String "WaitingForPubKey"

instance FromJSON OwnPubKeyRequest where
    parseJSON =
        withText "OwnPubKeyRequest" $ \case
            "WaitingForPubKey" -> pure WaitingForPubKey
            other              -> fail $ "Invalid constructor: " <> Text.unpack other

deriving via (PrettyShow OwnPubKeyRequest) instance Pretty OwnPubKeyRequest

-- | Get a public key belonging to the wallet that runs this contract.
--   * Any funds paid to this public key will be treated as the wallet's own
--     funds
--   * The wallet is able to sign transactions with the private key of this
--     public key, for example, if the public key is added to the
--     'requiredSignatures' field of 'Tx'.
--   * There is a 1-n relationship between wallets and public keys (although in
--     the mockchain n=1)
ownPubKey :: forall w s e. (AsContractError e, HasOwnPubKey s) => Contract w s e PubKey
ownPubKey = requestMaybe @w @OwnPubKeySym @_ @_ @s WaitingForPubKey Just

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
