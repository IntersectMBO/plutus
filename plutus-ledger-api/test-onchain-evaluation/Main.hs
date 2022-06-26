{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

module Main (main) where

import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise qualified as CBOR
import Control.Concurrent.Async (mapConcurrently)
import Control.Exception (evaluate)
import Control.Monad.Extra (whenJust)
import Data.List.NonEmpty (NonEmpty, nonEmpty, toList)
import Data.Maybe (catMaybes)
import PyF (fmt)
import System.Directory.Extra (listFiles)
import System.Environment (getEnv)
import System.FilePath (isExtensionOf, takeBaseName)
import Test.Tasty
import Test.Tasty.HUnit

data TestFailure
    = InvalidResult UnexpectedEvaluationResult
    | MissingCostParametersFor LedgerPlutusVersion

renderTestFailure :: TestFailure -> String
renderTestFailure = \case
    InvalidResult err -> display err
    MissingCostParametersFor ver ->
        [fmt|
Missing cost parameters for {show ver}. Report this as a bug
against the script dumper in plutus-apps."
|]

renderTestFailures :: NonEmpty TestFailure -> String
renderTestFailures xs =
    [fmt|
Number of failed test cases: {length xs}
{unlines . fmap renderTestFailure $ toList xs}
|]

-- | Test cases from a single event dump file
testOneFile :: FilePath -> TestTree
testOneFile eventFile = testCase (takeBaseName eventFile) $ do
    events <- CBOR.readFileDeserialise @ScriptEvaluationEvents eventFile

    case ( mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
         , mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
         ) of
        (Right ctxV1, Right ctxV2) -> do
            errs <-
                fmap catMaybes $
                    mapConcurrently
                        (evaluate . runSingleEvent ctxV1 ctxV2)
                        (toList (eventsEvents events))
            whenJust (nonEmpty errs) $ assertFailure . renderTestFailures
        (Left err, _) -> assertFailure $ display err
        (_, Left err) -> assertFailure $ display err
  where
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) <$> f costParams

    runSingleEvent ctxV1 ctxV2 event =
        case event of
            PlutusV1Event{} -> case ctxV1 of
                Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
                Nothing            -> Just $ MissingCostParametersFor PlutusV1
            PlutusV2Event{} -> case ctxV2 of
                Just (ctx, params) -> InvalidResult <$> checkEvaluationEvent ctx params event
                Nothing            -> Just $ MissingCostParametersFor PlutusV2

main :: IO ()
main = do
    dir <- getEnv "EVENT_DUMP_DIR"
    eventFiles <- filter ("event" `isExtensionOf`) <$> listFiles dir
    defaultMain . testGroup "Mainnet script evaluation test" $ fmap testOneFile eventFiles
