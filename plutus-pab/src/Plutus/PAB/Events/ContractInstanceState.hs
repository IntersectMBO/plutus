{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Plutus.PAB.Events.ContractInstanceState(
    PartiallyDecodedResponse(..)
    , toResp
    , fromResp
    , hasActiveRequests
    ) where

import           Control.Monad.Freer.Extras.Log (LogMessage)
import           Data.Aeson                     (FromJSON, ToJSON (..), Value)
import qualified Data.Aeson.Encode.Pretty       as JSON
import qualified Data.ByteString.Lazy.Char8     as BS8
import qualified Data.Text                      as Text
import           Data.Text.Extras               (abbreviate)
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                   (Generic)
import qualified Plutus.Contract.Resumable      as Contract
import qualified Plutus.Contract.State          as Contract

-- TODO: Replace with type synonym for @ContractResponse Value Value Value h@
data PartiallyDecodedResponse v =
    PartiallyDecodedResponse
        { newState        :: Contract.State Value
        , hooks           :: [Contract.Request v]
        , logs            :: [LogMessage Value]
        , lastLogs        :: [LogMessage Value] -- The log messages returned by the last step ('lastLogs' is a suffix of 'logs')
        , err             :: Maybe Value
        , observableState :: Value
        }
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)


toResp :: PartiallyDecodedResponse v -> Contract.ContractResponse Value Value Value v
toResp PartiallyDecodedResponse{newState, hooks, logs, err, observableState, lastLogs} =
    Contract.ContractResponse{Contract.newState = newState, Contract.hooks=hooks, Contract.logs=logs, Contract.err=err, Contract.observableState=observableState, Contract.lastLogs=lastLogs}

fromResp :: Contract.ContractResponse Value Value Value v -> PartiallyDecodedResponse v
fromResp Contract.ContractResponse{Contract.newState, Contract.hooks, Contract.logs, Contract.err, Contract.observableState, Contract.lastLogs} =
    PartiallyDecodedResponse{newState, hooks, logs, err, observableState, lastLogs}

instance Pretty v => Pretty (PartiallyDecodedResponse v) where
    pretty PartiallyDecodedResponse {newState, hooks} =
        vsep
            [ "State:"
            , indent 2 $ pretty $ abbreviate 120 $ Text.pack $ BS8.unpack $ JSON.encodePretty newState
            , "Hooks:"
            , indent 2 (vsep $ pretty <$> hooks)
            ]

-- | Whether the instance has any active requests
hasActiveRequests :: forall a. PartiallyDecodedResponse a -> Bool
hasActiveRequests = not . null . hooks
