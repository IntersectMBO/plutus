{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC   -Wno-orphans #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Control.Monad                  (void)
import           Control.Monad.Logger           (LoggingT, runStderrLoggingT)
import           Control.Monad.State            (StateT, evalStateT)
import qualified Data.Set                       as Set
import           Eventful                       (Aggregate, Projection, StreamEvent (StreamEvent), VersionedStreamEvent,
                                                 aggregateCommandHandler, aggregateProjection, commandStoredAggregate,
                                                 getLatestStreamProjection, latestProjection, nil, projectionSeed)
import           Eventful.Store.Memory          (EventMap, emptyEventMap, stateEventStoreReader, stateEventStoreWriter,
                                                 stateGlobalEventStoreReader)
import           Ledger.Value                   (isZero)
import           Plutus.SCB.Command             (saveTxAggregate)
import           Plutus.SCB.Core
import           Plutus.SCB.Events              (ChainEvent)
import qualified Plutus.SCB.Query               as Query
import           Test.QuickCheck.Instances.UUID ()
import           Test.Tasty                     (TestTree, testGroup)
import           Test.Tasty.HUnit               (assertEqual, assertFailure, testCase)
import           Test.Tasty.QuickCheck          (property, testProperty)

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
        [ testCase "Initially there are no contracts installed" $ do
              installed <- runScenario installedContracts
              assertEqual "" 0 $ Set.size installed
        , testCase "Initially there are no contracts active" $ do
              active <- runScenario activeContracts
              assertEqual "" 0 $ Set.size active
        , testCase
              "Installing a contract successfully increases the installed contract count." $ do
              (installation, installed, active) <-
                  runScenario $ do
                      installationResult <- installContract "/bin/sh"
                      installed <- installedContracts
                      active <- activeContracts
                      pure (installationResult, installed, active)
              assertRight installation
              assertEqual "" 1 $ Set.size installed
              assertEqual "" 0 $ Set.size active
        , testCase "We can activate a contract." $ do
              (installation, activation, installed, active) <-
                  runScenario $ do
                      installationResult <-
                          installContract
                              "/Users/kris/.local/bin/plutus-contract"
                      installed <- installedContracts
                      activationResult <-
                          activateContract
                              "/Users/kris/.local/bin/plutus-contract"
                      active <- activeContracts
                      pure
                          ( installationResult
                          , activationResult
                          , installed
                          , active)
              assertRight installation
              assertRight activation
              assertEqual "" 1 $ Set.size installed
              assertEqual "" 1 $ Set.size active
        ]
  where
    runScenario :: StateT (EventMap ChainEvent) (LoggingT IO) a -> IO a
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

assertRight :: Show e => Either e a -> IO ()
assertRight (Right _) = pure ()
assertRight (Left value) =
    void $
    assertFailure $ "Expected (Right _), got: (Left " <> show value <> ")"
