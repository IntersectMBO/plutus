{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MonoLocalBinds             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
-- | Dealing with instances of running contract.
module Language.Plutus.Contract.Effects.Instance(
    HasOwnId
    , ContractInstanceId
    , ownInstanceId
    , OwnIdRequest(..)
    , OwnId
    , event
    , request
    ) where

import           Data.Aeson                       (FromJSON (..), ToJSON (..))
import qualified Data.Aeson                       as JSON
import           Data.Row
import qualified Data.Text                        as Text
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           GHC.Generics                     (Generic)

import           Language.Plutus.Contract.Request (ContractRow, requestMaybe)
import           Language.Plutus.Contract.Schema  (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Types   (AsContractError, Contract)
import           Wallet.Types                     (ContractInstanceId)

type OwnIdSym = "own-instance-id"

type HasOwnId s =
  ( HasType OwnIdSym ContractInstanceId (Input s)
  , HasType OwnIdSym OwnIdRequest (Output s)
  , ContractRow s)

type OwnId = OwnIdSym .== (ContractInstanceId, OwnIdRequest)

data OwnIdRequest = WaitingForInstanceId
  deriving stock (Eq, Show, Generic)

-- TODO Aeson encodes this single no-arg constructor as, '{ tag:
-- OwnPubKey, contents: [] }', which our PureScript decoders can't
-- handle.
-- The correct fix is on the PureScript side - because we consider
-- whatever Aeson does to be canon - but for now this is equivalent
-- and faster.
instance ToJSON OwnIdRequest where
    toJSON WaitingForInstanceId = JSON.String "WaitingForInstanceId"

instance FromJSON OwnIdRequest where
    parseJSON =
        JSON.withText "OwnIdRequest" $ \case
            "WaitingForInstanceId" -> pure WaitingForInstanceId
            other                  -> fail $ "Invalid constructor: " <> Text.unpack other

deriving via (PrettyShow OwnIdRequest) instance Pretty OwnIdRequest

-- | Get the 'ContractInstanceId' of this instance.
ownInstanceId :: forall w s e. (AsContractError e, HasOwnId s) => Contract w s e ContractInstanceId
ownInstanceId = requestMaybe @w @OwnIdSym @_ @_ @s WaitingForInstanceId Just

event
    :: forall s.
    ( HasOwnId s )
    => ContractInstanceId
    -> Event s
event = Event . IsJust (Label @OwnIdSym)

request
    :: forall s.
    ( HasOwnId s )
    => Handlers s
    -> Maybe OwnIdRequest
request (Handlers r) = trial' r (Label @OwnIdSym)
