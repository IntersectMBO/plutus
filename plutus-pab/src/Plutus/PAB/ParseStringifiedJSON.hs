{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Plutus.PAB.ParseStringifiedJSON(
    UnStringifyJSONLog(..),
    parseStringifiedJSON
    ) where

import           Cardano.BM.Data.Tracer         (ToObject)
import           Cardano.BM.Data.Tracer.Extras  (PrettyToObject (..))
import           Control.Monad.Freer
import           Control.Monad.Freer.Extras.Log (LogMsg, logDebug)
import           Data.Aeson                     (FromJSON, ToJSON, Value (..), decode)
import qualified Data.ByteString.Lazy.Char8     as LBS
import qualified Data.Text.Encoding             as Text
import           Data.Text.Prettyprint.Doc      (Pretty (..))
import           GHC.Generics                   (Generic)

data UnStringifyJSONLog =
    ParseStringifiedJSONAttempt
    | ParseStringifiedJSONFailed
    | ParseStringifiedJSONSuccess
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)
    deriving ToObject via (PrettyToObject UnStringifyJSONLog)

instance Pretty UnStringifyJSONLog where
    pretty = \case
        ParseStringifiedJSONAttempt -> "parseStringifiedJSON: Attempting to remove 1 layer StringifyJSON"
        ParseStringifiedJSONFailed  -> "parseStringifiedJSON: Failed, returning original string"
        ParseStringifiedJSONSuccess -> "parseStringifiedJSON: Succeeded"

parseStringifiedJSON ::
    forall effs.
    Member (LogMsg UnStringifyJSONLog) effs
    => Value
    -> Eff effs Value
parseStringifiedJSON v = case v of
    String s -> do
        logDebug ParseStringifiedJSONAttempt
        let s' = decode @Value $ LBS.fromStrict $ Text.encodeUtf8 s
        case s' of
            Nothing -> do
                logDebug ParseStringifiedJSONFailed
                pure v
            Just s'' -> do
                logDebug ParseStringifiedJSONSuccess
                pure s''
    _ -> pure v
