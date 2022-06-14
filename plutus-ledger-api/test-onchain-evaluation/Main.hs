{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Codec.Serialise qualified as CBOR
import Control.Concurrent.ParallelIO.Local qualified as Concurrent
import Control.Exception (evaluate)
import Data.ByteString.Base16 qualified as B16
import Data.ByteString.Lazy qualified as Lazy
import Data.Foldable (for_)
import Data.List (intercalate)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import Options.Applicative qualified as OA
import Plutus.Script.Evaluation.Test.Options qualified as O
import PlutusCore.Evaluation.Machine.CostModelInterface (CostModelApplyError)
import PlutusLedgerApi.Test.EvaluationEvent (ScriptEvaluationData (..), ScriptEvaluationEvent (..),
                                             ScriptEvaluationResult (..))
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PyF (fmt)
import System.Directory.Extra (listFiles)
import System.Exit (die)
import System.FilePath (isExtensionOf, (<.>))
import System.IO.Extra (withTempDir)
import System.Process.Extra (system_)

data TestFailure
    = InvalidEvaluationResult
        Text
        -- ^ Serialised `ScriptEvaluationEvent`
        ScriptEvaluationResult
    | InvalidCostParams
        Text
        -- ^ Serialised `ScriptEvaluationEvent`
        CostModelApplyError
    deriving stock (Show)

main :: IO ()
main = do
    opts <- OA.execParser O.parserInfo
    let extZipped = O.optsEventFileExt opts <.> "bz2"
    withTempDir $ \dir -> do
        putStrLn "Downloading event dump files"
        let s3DownloadCmd :: String
            s3DownloadCmd = [fmt|{keyId} {secretKey} {region} aws {endpoint} s3 cp {s3Path} {dir} {options}|]
              where
                keyId = [fmt|AWS_ACCESS_KEY_ID={O.optsS3AccessKeyId opts}|]
                secretKey = [fmt|AWS_SECRET_ACCESS_KEY={O.optsS3SecretAccessKey opts}|]
                region = [fmt|AWS_DEFAULT_REGION={O.optsS3Region opts}|]
                endpoint = [fmt|--endpoint-url {O.optsS3Endpoint opts}|]
                s3Path = [fmt|s3://{O.optsS3Bucket opts}/{O.optsS3Prefix opts}|]
                options = [fmt|--recursive --exclude "*" --include "*.{extZipped}"|]
        putStrLn $ "Running: " <> s3DownloadCmd
        -- It would be better to use amazonka, but the version bounds don't quite line up
        -- (e.g., amazonka-core has aeson <1.6)
        system_ s3DownloadCmd
        eventFilesZipped <- filter (extZipped `isExtensionOf`) <$> listFiles dir
        for_ eventFilesZipped $ \zipped -> do
            putStrLn $ "Unzipping " <> zipped
            system_ $ "bunzip2 " <> zipped
        eventFiles <- filter (O.optsEventFileExt opts `isExtensionOf`) <$> listFiles dir
        for_ (zip [1 :: Int ..] eventFiles) $ \(i, eventFile) -> do
            putStrLn [fmt|Processing event file {i}: {eventFile}|]
            events <- CBOR.readFileDeserialise @[ScriptEvaluationEvent] eventFile
            mbErrs <- Concurrent.withPool (O.optsConcurrency opts) $ \pool -> do
                Concurrent.parallel pool $ fmap (evaluate . checkEvaluationEvent) events
            case catMaybes mbErrs of
                [] -> putStrLn "All tests passed"
                errs ->
                    die
                        [fmt|
Script evaluation regression test failed.
Number of failed test cases: {length errs}
{intercalate "\n" (show <$> errs)}
|]

checkEvaluationEvent :: ScriptEvaluationEvent -> Maybe TestFailure
checkEvaluationEvent ev = case ev of
    PlutusV1Event ScriptEvaluationData{..} expected ->
        case V1.mkEvaluationContext dataCostParams of
            Left err -> Just $ InvalidCostParams ev' err
            Right ctx ->
                let (_, actual) =
                        V1.evaluateScriptRestricting
                            dataProtocolVersion
                            V1.Quiet
                            ctx
                            dataBudget
                            dataScript
                            dataInputs
                 in case (expected, actual) of
                        (ScriptEvaluationSuccess, Left _) ->
                            Just $ InvalidEvaluationResult ev' ScriptEvaluationFailure
                        (ScriptEvaluationFailure, Right _) ->
                            Just $ InvalidEvaluationResult ev' ScriptEvaluationSuccess
                        _ -> Nothing
    PlutusV2Event ScriptEvaluationData{..} expected ->
        case V2.mkEvaluationContext dataCostParams of
            Left err -> Just $ InvalidCostParams ev' err
            Right ctx ->
                let (_, actual) =
                        V2.evaluateScriptRestricting
                            dataProtocolVersion
                            V2.Quiet
                            ctx
                            dataBudget
                            dataScript
                            dataInputs
                 in case (expected, actual) of
                        (ScriptEvaluationSuccess, Left _) ->
                            Just $ InvalidEvaluationResult ev' ScriptEvaluationFailure
                        (ScriptEvaluationFailure, Right _) ->
                            Just $ InvalidEvaluationResult ev' ScriptEvaluationSuccess
                        _ -> Nothing
  where
    ev' :: Text
    ev' = Text.decodeLatin1 . B16.encode . Lazy.toStrict $ CBOR.serialise ev
