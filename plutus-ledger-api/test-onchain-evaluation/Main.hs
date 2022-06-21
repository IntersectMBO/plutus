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
import Test.Tasty.Providers

data SingleTest
    = SingleTest
        LedgerPlutusVersion
        (Maybe (EvaluationContext, [Integer]))
        ScriptEvaluationEvent

instance IsTest SingleTest where
    run _opts (SingleTest ver mbCtx ev) _reportProgress = case mbCtx of
        Just (ctx, params) ->
            evaluate
                =<< ( pure . maybe (testPassed mempty) (testFailed . display) $
                        checkEvaluationEvent ctx params ev
                    )
        Nothing -> pure . testFailed $ "missing cost parameters for " <> show ver

    testOptions = mempty

-- | Test cases from a single event dump file
testOneFile :: TestName -> ScriptEvaluationEvents -> TestTree
testOneFile name events =
    case ( mkContext V1.mkEvaluationContext (eventsCostParamsV1 events)
         , mkContext V2.mkEvaluationContext (eventsCostParamsV2 events)
         ) of
        (Right ctxV1, Right ctxV2) ->
            testGroup name $
                fmap
                    ( \(idx, event) ->
                        singleTest ("test case " <> show idx) $ case event of
                            PlutusV1Event{} -> SingleTest PlutusV1 ctxV1 event
                            PlutusV2Event{} -> SingleTest PlutusV2 ctxV2 event
                    )
                    (zip [1 :: Int ..] (toList (eventsEvents events)))
        (Left err, _) ->
            testCase name . assertFailure $ display err
        (_, Left err) ->
            testCase name . assertFailure $ display err
  where
    mkContext f = \case
        Nothing         -> Right Nothing
        Just costParams -> Just . (,costParams) <$> f costParams

main :: IO ()
main = do
    dir <- getEnv "EVENT_DUMP_DIR"
    eventFiles <- filter ("event" `isExtensionOf`) <$> listFiles dir
    eventss <- traverse (CBOR.readFileDeserialise @ScriptEvaluationEvents) eventFiles
    defaultMain . testGroup "Mainnet script evaluation test" . fmap (uncurry testOneFile) $
        zip eventFiles eventss
