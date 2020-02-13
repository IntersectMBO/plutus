{-# LANGUAGE OverloadedStrings #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Control.Monad                                 (void)
import           Control.Monad.IO.Class                        (liftIO)
import           Data.Aeson                                    as JSON
import qualified Data.Set                                      as Set
import           Eventful                                      (globalStreamProjection, streamProjectionState)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game
import           Ledger.Ada                                    (lovelaceValueOf)
import           Plutus.SCB.Command                            ()
import           Plutus.SCB.Core
import           Plutus.SCB.TestApp                            (runScenario)
import           Test.QuickCheck.Instances.UUID                ()
import           Test.Tasty                                    (TestTree, testGroup)
import           Test.Tasty.HUnit                              (assertEqual, testCase)

tests :: TestTree
tests = testGroup "SCB.Core" [installContractTests, executionTests]

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
              "Installing a contract successfully increases the installed contract count" $
          runScenario $ do
              installContract "/bin/sh"
              --
              installed <- installedContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              active <- activeContracts
              liftIO $ assertEqual "" 0 $ Set.size active
        , testCase "We can activate a contract" $
          runScenario $ do
              installContract "game"
              --
              installed <- installedContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              void $ activateContract "game"
              --
              active <- activeContracts
              liftIO $ assertEqual "" 1 $ Set.size active
        ]

executionTests :: TestTree
executionTests =
    testGroup
        "Executing contracts."
        [ testCase "Locked Game" $
          runScenario $ do
              installContract "game"
              uuid <- activateContract "game"
              updateContract
                  uuid
                  "lock"
                  (toJSON
                       (Contracts.Game.LockParams
                            { Contracts.Game.amount = lovelaceValueOf 15
                            , Contracts.Game.secretWord = "password"
                            }))
              txs <-
                  streamProjectionState <$>
                  refreshProjection (globalStreamProjection txHistoryProjection)
              liftIO $
                  assertEqual "Contains one balanced transaction" 1 $ length txs
        ]
