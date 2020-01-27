{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Eventful                       (Aggregate, Projection, StreamEvent (StreamEvent), VersionedStreamEvent,
                                                 aggregateCommandHandler, aggregateProjection, latestProjection, nil,
                                                 projectionSeed)
import           Ledger.Value                   (isZero)
import           Plutus.SCB.Command             (saveTxAggregate)
import qualified Plutus.SCB.Query               as Query
import           Test.QuickCheck.Instances.UUID ()
import           Test.Tasty                     (TestTree, testGroup)
import           Test.Tasty.QuickCheck          (property, testProperty)

tests :: TestTree
tests = testGroup "SCB.Core" [eventCountTests, trialBalanceTests]

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
