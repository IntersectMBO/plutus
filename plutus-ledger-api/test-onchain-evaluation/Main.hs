{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

module Main (main) where

import Plutus.Script.Evaluation.Test.Options qualified as O
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise qualified as CBOR
import Control.Concurrent.ParallelIO.Local qualified as Concurrent
import Control.Exception (evaluate)
import Control.Monad.Extra (whenJust)
import Data.List.Extra (nubOrd)
import Data.List.NonEmpty (NonEmpty, nonEmpty, toList)
import Data.Maybe
import Data.String (fromString)
import Data.Text (Text)
import Data.Traversable (for)
import Options.Applicative qualified as OA
import PlutusCore.Pretty
import PlutusPrelude (reoption)
import Prettyprinter
import PyF (fmt)
import System.Directory.Extra (listFiles)
import System.Exit (die)
import System.FilePath (isExtensionOf)

-- | All test failures in a single event dump file
data TestFailures
    = InvalidResults FilePath (NonEmpty UnexpectedEvaluationResult)
    | MissingCostParameters FilePath (NonEmpty LedgerPlutusVersion)
    deriving stock (Show)

instance Pretty TestFailures where
    pretty = \case
        InvalidResults eventsFile errs ->
            nest 2 $
                vsep
                    [ "Test Failures in" <+> pretty eventsFile
                    , vsep (pretty <$> toList errs)
                    ]
        MissingCostParameters eventsFile ver ->
            "Missing cost parameters for" <+> fromString (show ver) <+> "in" <+> pretty eventsFile

data TestFailure
    = InvalidResult UnexpectedEvaluationResult
    | MissingCostParametersFor LedgerPlutusVersion

main :: IO ()
main = do
    opts <- OA.execParser O.parserInfo
    eventFiles <- filter (O.optsEventFileExt opts `isExtensionOf`) <$> listFiles (O.optsDir opts)
    errs <- fmap concat . for (zip [1 :: Int ..] eventFiles) $ \(i, eventFile) -> do
        putStrLn [fmt|Processing event file {i}: {eventFile}|]
        -- Each event dump file serialises a `ScriptEvaluationEvents`.
        events <- CBOR.readFileDeserialise @ScriptEvaluationEvents eventFile
        ctxV1 <-
            either invalidCostParams pure $
                mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
        ctxV2 <-
            either invalidCostParams pure $
                mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
        errs <- fmap catMaybes . Concurrent.withPool (O.optsConcurrency opts) $ \pool -> do
            Concurrent.parallel pool $ fmap (evaluate . runTest ctxV1 ctxV2) (toList (eventsEvents events))
        let invalidResults = concatMap (\case InvalidResult r -> [r]; _ -> []) errs
            missingCostParams = nubOrd $ concatMap (\case MissingCostParametersFor ver -> [ver]; _ -> []) errs
            failures :: [TestFailures]
            failures =
                (InvalidResults eventFile <$> reoption (nonEmpty invalidResults))
                    <> (MissingCostParameters eventFile <$> reoption (nonEmpty missingCostParams))

        whenJust (nonEmpty invalidResults) $ \xs -> do
            putStrLn
                [fmt|
Some tests failed. Number of failures: {length xs}
{render . indent 2 . vsep $ pretty <$> toList xs :: Text}
|]
        whenJust (nonEmpty missingCostParams) $ \vers -> do
            putStrLn
                [fmt|
Missing cost parameters for: {show (toList vers)}
|]
        pure failures
    case errs of
        [] -> pure ()
        _ ->
            die
                [fmt|
Test failures:
{render . indent 2 . vsep $ pretty <$> errs :: Text}
|]
  where
    runTest ::
        Maybe (EvaluationContext, [Integer]) ->
        Maybe (EvaluationContext, [Integer]) ->
        ScriptEvaluationEvent ->
        Maybe TestFailure
    runTest ctxV1 ctxV2 event = case event of
        PlutusV1Event{} -> case ctxV1 of
            Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
            Nothing            -> Just $ MissingCostParametersFor PlutusV1
        PlutusV2Event{} -> case ctxV2 of
            Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
            Nothing            -> Just $ MissingCostParametersFor PlutusV2
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) <$> f costParams

    invalidCostParams err = die $ "Invalid cost parameters: " <> show err
