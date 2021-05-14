{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
module Plutus.PAB.Events.ContractInstanceState(
    PartiallyDecodedResponse(..)
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
        { hooks           :: [Contract.Request v]
        , logs            :: [LogMessage Value]
        , lastLogs        :: [LogMessage Value] -- The log messages returned by the last step ('lastLogs' is a suffix of 'logs')
        , err             :: Maybe Value
        , observableState :: Value
        }
    deriving (Show, Eq, Generic, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)

fromResp :: Contract.ContractResponse Value Value Value v -> PartiallyDecodedResponse v
fromResp Contract.ContractResponse{Contract.hooks, Contract.logs, Contract.err, Contract.observableState, Contract.lastLogs} =
    PartiallyDecodedResponse{hooks, logs, err, observableState, lastLogs}

instance Pretty v => Pretty (PartiallyDecodedResponse v) where
    pretty PartiallyDecodedResponse {hooks, observableState} =
        vsep
            [ "State:"
            , indent 2 $ pretty $ abbreviate 120 $ Text.pack $ BS8.unpack $ JSON.encodePretty observableState
            , "Hooks:"
            , indent 2 (vsep $ pretty <$> hooks)
            ]

-- | Whether the instance has any active requests
hasActiveRequests :: forall w s e a. Contract.ContractResponse w e s a -> Bool
hasActiveRequests = not . null . Contract.hooks
