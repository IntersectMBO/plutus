{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Control.Monad                                 (void)
import           Control.Monad.IO.Class                        (MonadIO, liftIO)
import           Control.Monad.Logger                          (LoggingT, runStderrLoggingT)
import           Control.Monad.State                           (StateT, evalStateT)
import           Data.Aeson                                    as JSON
import           Data.Aeson.Types                              as JSON
import           Data.Bifunctor                                (first)
import qualified Data.Set                                      as Set
import           Data.Text                                     (Text)
import qualified Data.Text                                     as Text
import           Eventful                                      (Aggregate, Projection, StreamEvent (StreamEvent),
                                                                VersionedStreamEvent, aggregateCommandHandler,
                                                                aggregateProjection, commandStoredAggregate,
                                                                getLatestStreamProjection, latestProjection, nil,
                                                                projectionSeed)
import           Eventful.Store.Memory                         (EventMap, emptyEventMap, stateEventStoreReader,
                                                                stateEventStoreWriter, stateGlobalEventStoreReader)
import           Language.Plutus.Contract.Resumable            (ResumableError)
import           Language.Plutus.Contract.Servant              (initialResponse, runUpdate)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game
import           Ledger.Value                                  (isZero)
import           Plutus.SCB.Command                            (saveTxAggregate)
import           Plutus.SCB.Core
import           Plutus.SCB.Events                             (ChainEvent)
import qualified Plutus.SCB.Query                              as Query
import           Plutus.SCB.Types                              (SCBError (ContractCommandError, ContractNotFound))
import           Test.QuickCheck.Instances.UUID                ()
import           Test.Tasty                                    (TestTree, testGroup)
import           Test.Tasty.HUnit                              (HasCallStack, assertEqual, assertFailure, testCase)
import           Test.Tasty.QuickCheck                         (property, testProperty)

tests :: TestTree
tests =
    testGroup
        "SCB.Core"
        [eventCountTests, trialBalanceTests, installContractTests]

eventCountTests :: TestTree
eventCountTests =
    testGroup
        "saveTx/eventCount"
        [ testProperty "Overall balance is always 0" $ \txs ->
              property $
              isZero $
              runCommandQueryChain saveTxAggregate Query.trialBalance txs
        ]

trialBalanceTests :: TestTree
trialBalanceTests =
    testGroup
        "saveTx/trialBalance"
        [ testProperty "Overall balance is always 0" $ \txs ->
              property $
              isZero $
              runCommandQueryChain saveTxAggregate Query.trialBalance txs
        ]

installContractTests :: TestTree
installContractTests =
    testGroup
        "installContract scenario"
        [ testCase "Initially there are no contracts installed" $
          runScenario $ do
              installed <- installedContracts
              liftIO $ assertEqual "" 0 $ Set.size installed
        , testCase "Initially there are no contracts active" $
          runScenario $ do
              active <- activeContracts
              liftIO $ assertEqual "" 0 $ Set.size active
        , testCase
              "Installing a contract successfully increases the installed contract count." $
          runScenario $ do
              installContract "/bin/sh"
              --
              installed <- installedContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              active <- activeContracts
              liftIO $ assertEqual "" 0 $ Set.size active
        , testCase "We can activate a contract." $
          runScenario $ do
              installContract "game"
              --
              installed <- installedContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              activationResult <- activateContract "game"
              liftIO $ assertRight activationResult
              --
              active <- activeContracts
              liftIO $ assertEqual "" 1 $ Set.size active
        ]
  where
    runScenario ::
           MonadIO m => StateT (EventMap ChainEvent) (LoggingT m) a -> m a
    runScenario action = runStderrLoggingT $ evalStateT action emptyEventMap

runCommandQueryChain ::
       Aggregate aState event command
    -> Projection pState (VersionedStreamEvent event)
    -> [command]
    -> pState
runCommandQueryChain aggregate projection commands =
    latestProjection projection $
    fmap (StreamEvent nil 1) $
    foldMap
        (aggregateCommandHandler
             aggregate
             (projectionSeed (aggregateProjection aggregate)))
        commands

instance Monad m => MonadEventStore event (StateT (EventMap event) m) where
    refreshProjection = getLatestStreamProjection stateGlobalEventStoreReader
    runAggregateCommand =
        commandStoredAggregate stateEventStoreWriter stateEventStoreReader

instance Monad m => MonadContract (StateT state m) where
    invokeContract (InitContract "game") =
        pure $ do
            value <- bar $ initialResponse Contracts.Game.game
            foo $ JSON.eitherDecode (JSON.encode value)
    invokeContract (UpdateContract "game" payload) =
        pure $ do
            request <- foo $ JSON.parseEither JSON.parseJSON payload
            value <- bar $ runUpdate Contracts.Game.game request
            foo $ JSON.eitherDecode (JSON.encode value)
    invokeContract (InitContract contractPath) =
        pure $ Left $ ContractNotFound contractPath
    invokeContract (UpdateContract contractPath _) =
        pure $ Left $ ContractNotFound contractPath

foo :: Either String a -> Either SCBError a
foo = first (ContractCommandError 0 . Text.pack)

bar :: Either (ResumableError Text) a -> Either SCBError a
bar = first (ContractCommandError 0 . Text.pack . show)

assertRight :: (HasCallStack, Show e) => Either e a -> IO ()
assertRight (Right _) = pure ()
assertRight (Left value) =
    void $
    assertFailure $ "Expected (Right _), got: (Left " <> show value <> ")"
