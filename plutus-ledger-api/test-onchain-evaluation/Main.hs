{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

module Main (main) where

import PlutusCore.Pretty
import PlutusLedgerApi.Common
import PlutusLedgerApi.Test.EvaluationEvent
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2

import Codec.Serialise qualified as CBOR
import Control.Exception (evaluate)
import Data.Foldable (toList)
import System.Directory.Extra (listFiles)
import System.Environment (getEnv)
import System.FilePath (isExtensionOf)
import Test.Tasty
import Test.Tasty.HUnit

-- | Test cases from a single event dump file
testOneFile :: FilePath -> IO TestTree
testOneFile eventFile = do
    events <- CBOR.readFileDeserialise @ScriptEvaluationEvents eventFile
    ctxV1 <-
        either (assertFailure . display) pure $
            mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
    ctxV2 <-
        either (assertFailure . display) pure $
            mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
    pure . testGroup eventFile $
        fmap
            ( \(idx, event) ->
                testCase ("test case " <> show idx) $
                    evaluate =<< runTest ctxV1 ctxV2 event
            )
            (zip [1 :: Int ..] (toList (eventsEvents events)))
  where
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) <$> f costParams

    runTest ::
        Maybe (EvaluationContext, [Integer]) ->
        Maybe (EvaluationContext, [Integer]) ->
        ScriptEvaluationEvent ->
        Assertion
    runTest ctxV1 ctxV2 event = case event of
        PlutusV1Event{} -> case ctxV1 of
            Just (ctx, params) ->
                maybe (pure ()) (assertFailure . display) $ checkEvaluationEvent ctx params event
            Nothing -> assertFailure "missing cost parameters for PlutusV1"
        PlutusV2Event{} -> case ctxV2 of
            Just (ctx, params) ->
                maybe (pure ()) (assertFailure . display) $ checkEvaluationEvent ctx params event
            Nothing -> assertFailure "missing cost parameters for PlutusV2"

main :: IO ()
main = do
    dir <- getEnv "EVENT_DUMP_DIR"
    eventFiles <- filter ("event" `isExtensionOf`) <$> listFiles dir
    defaultMain . testGroup "Mainnet script evaluation test" =<< traverse testOneFile eventFiles
