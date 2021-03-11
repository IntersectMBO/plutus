{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Plutus.PAB.Events.ContractInstanceState(
    ContractInstanceState(..)
    , PartiallyDecodedResponse(..)
    , toResp
    , fromResp
    , hasActiveRequests
    ) where

import           Control.Monad.Freer.Extras.Log     (LogMessage)
import           Data.Aeson                         (FromJSON, ToJSON (..), Value, object, (.:), (.=))
import qualified Data.Aeson.Encode.Pretty           as JSON
import qualified Data.ByteString.Lazy.Char8         as BS8
import qualified Data.Text                          as Text
import           Data.Text.Extras                   (abbreviate)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                       (Generic)
import           Plutus.Contract.Resumable (IterationID)
import qualified Plutus.Contract.Resumable as Contract
import qualified Plutus.Contract.State     as Contract
import           Plutus.PAB.Effects.Contract        (PABContract (..))
import           Plutus.PAB.Events.Contract         (ContractPABRequest, ContractResponse (..))
import           Wallet.Types                       (ContractInstanceId)

-- TODO: Replace with type synonym for @ContractResponse Value Value Value h@
data PartiallyDecodedResponse v =
    PartiallyDecodedResponse
        { newState        :: Contract.State Value
        , hooks           :: [Contract.Request v]
        , logs            :: [LogMessage Value]
        , err             :: Maybe Value
        , observableState :: Value
        }
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)


toResp :: PartiallyDecodedResponse v -> Contract.ContractResponse Value Value Value v
toResp PartiallyDecodedResponse{newState, hooks, logs, err, observableState} =
    Contract.ContractResponse{Contract.newState = newState, Contract.hooks=hooks, Contract.logs=logs, Contract.err=err, Contract.observableState=observableState}

fromResp :: Contract.ContractResponse Value Value Value v -> PartiallyDecodedResponse v
fromResp Contract.ContractResponse{Contract.newState, Contract.hooks, Contract.logs, Contract.err, Contract.observableState} =
    PartiallyDecodedResponse{newState, hooks, logs, err, observableState}

instance Pretty v => Pretty (PartiallyDecodedResponse v) where
    pretty PartiallyDecodedResponse {newState, hooks} =
        vsep
            [ "State:"
            , indent 2 $ pretty $ abbreviate 120 $ Text.pack $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 (vsep $ pretty <$> hooks)
            ]

-- | FIXME: Delete?
data ContractInstanceState t =
    ContractInstanceState
        { csContract           :: ContractInstanceId
        , csCurrentIteration   :: IterationID
        , csCurrentState       :: PartiallyDecodedResponse ContractPABRequest
        , csContractDefinition :: ContractDef t
        }
    deriving stock Generic

deriving stock instance (Show (ContractDef t)) => Show (ContractInstanceState t)
deriving stock instance (Eq (ContractDef t)) => Eq (ContractInstanceState t)
deriving anyclass instance (ToJSON (ContractDef t)) => ToJSON (ContractInstanceState t)
deriving anyclass instance (FromJSON (ContractDef t)) => FromJSON (ContractInstanceState t)

instance Pretty (ContractDef t) => Pretty (ContractInstanceState t) where
    pretty ContractInstanceState{csContract, csCurrentIteration, csCurrentState, csContractDefinition} =
        hang 2 $ vsep
            [ "Instance:" <+> pretty csContract
            , "Iteration:" <+> pretty csCurrentIteration
            , "State:" <+> pretty csCurrentState
            , "Contract definition:" <+> pretty csContractDefinition
            ]

-- | Whether the instance has any active requests
hasActiveRequests :: forall a. PartiallyDecodedResponse a -> Bool
hasActiveRequests = not . null . hooks
