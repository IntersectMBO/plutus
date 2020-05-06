{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Cardano.Node.Follower                         (NodeFollowerEffect)
import           Control.Lens                                  (view, _1)
import           Control.Monad                                 (void)
import           Control.Monad.Freer                           (Eff, LastMember, Member, Members)
import           Control.Monad.Freer.Error                     (Error)
import           Control.Monad.Freer.Extra.Log                 (Log)
import qualified Control.Monad.Freer.Log                       as EmulatorLog
import           Control.Monad.IO.Class                        (MonadIO, liftIO)
import           Data.Aeson                                    as JSON
import qualified Data.Set                                      as Set
import           Eventful                                      (UUID, globalStreamProjection, streamProjectionState)
import qualified Language.PlutusTx.Coordination.Contracts.Game as Contracts.Game
import           Ledger                                        (pubKeyAddress)
import           Ledger.Ada                                    (lovelaceValueOf)
import           Plutus.SCB.Command                            ()
import           Plutus.SCB.Core
import           Plutus.SCB.Effects.Contract                   (ContractEffect)
import           Plutus.SCB.Effects.ContractTest               (TestContracts (..))
import           Plutus.SCB.Effects.EventLog                   (EventLogEffect)
import           Plutus.SCB.Effects.MultiAgent                 (SCBClientEffects, agentAction, agentControlAction)
import           Plutus.SCB.Events                             (ChainEvent)
import           Plutus.SCB.Query                              (chainOverviewProjection)
import           Plutus.SCB.TestApp                            (defaultWallet, runScenario, sync, syncAll, valueAt)
import           Plutus.SCB.TestApp                            (runScenario, sync, valueAt)
import           Plutus.SCB.Types                              (SCBError)
import           Plutus.SCB.Types                              (SCBError, chainOverviewBlockchain)
import           Test.QuickCheck.Instances.UUID                ()
import           Test.Tasty                                    (TestTree, testGroup)
import           Test.Tasty.HUnit                              (HasCallStack, assertBool, assertEqual, testCase)
import           Wallet.API                                    (ChainIndexEffect, NodeClientEffect,
                                                                SigningProcessEffect, WalletAPIError, WalletEffect,
                                                                ownPubKey)
import           Wallet.API                                    (ownPubKey)
import           Wallet.Effects                                (WalletEffects)
import qualified Wallet.Emulator.Chain                         as Chain
import           Wallet.Emulator.ChainIndex                    (ChainIndexControlEffect)
import           Wallet.Emulator.NodeClient                    (NodeControlEffect)
import           Wallet.Emulator.SigningProcess                (SigningProcessControlEffect)
import           Wallet.Rollup                                 (doAnnotateBlockchain)
import           Wallet.Rollup.Types                           (DereferencedInput (DereferencedInput, InputNotFound),
                                                                dereferencedInputs, isFound)

tests :: TestTree
tests = testGroup "SCB.Core" [installContractTests, executionTests]

installContractTests :: TestTree
installContractTests =
    testGroup
        "installContract scenario"
        [ testCase "Initially there are no contracts installed" $
          runScenario $ do
              installed <- installedContracts @TestContracts
              liftIO $ assertEqual "" 0 $ Set.size installed
        , testCase "Initially there are no contracts active" $
          runScenario $ do
              active <- activeContracts @TestContracts
              liftIO $ assertEqual "" 0 $ Set.size active
        , testCase
              "Installing a contract successfully increases the installed contract count" $
          runScenario $ do
              installContract @TestContracts Game
              --
              installed <- installedContracts @TestContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              active <- activeContracts @TestContracts
              liftIO $ assertEqual "" 0 $ Set.size active
        , testCase "We can activate a contract" $
          runScenario $ do
              installContract Game
              --
              installed <- installedContracts @TestContracts
              liftIO $ assertEqual "" 1 $ Set.size installed
              --
              void $ agentAction defaultWallet (activateContract Game)
              --
              active <- activeContracts @TestContracts
              liftIO $ assertEqual "" 1 $ Set.size active
        ]

executionTests :: TestTree
executionTests =
    testGroup
        "Executing contracts."
        [ testCase "Guessing Game" $
          runScenario $ do
              let openingBalance = 10000
                  lockAmount = 15
              address <- pubKeyAddress <$> agentAction defaultWallet ownPubKey
              balance0 <- valueAt address
              liftIO $
                  assertEqual
                      "Check our opening balance."
                      (lovelaceValueOf openingBalance)
                      balance0
              installContract Game
              -- need to add contract address to wallet's watched addresses
              uuid <- agentAction defaultWallet (activateContract Game)
              syncAll
              assertTxCount
                  "Activating the game does not generate transactions."
                  0
              agentAction defaultWallet $ lock
                  uuid
                  Contracts.Game.LockParams
                      { Contracts.Game.amount = lovelaceValueOf lockAmount
                      , Contracts.Game.secretWord = "password"
                      }
              Chain.processBlock
              syncAll
              assertTxCount "Locking the game should produce one transaction" 1
              balance1 <- valueAt address
              liftIO $
                  assertEqual
                      "Locking the game should reduce our balance."
                      (lovelaceValueOf (openingBalance - lockAmount))
                      balance1
              agentAction defaultWallet $ guess
                  uuid
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "wrong"}
              Chain.processBlock
              syncAll
              assertTxCount "A wrong guess still produces a transaction." 2
              agentAction defaultWallet $ guess
                  uuid
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "password"}
              Chain.processBlock
              syncAll
              assertTxCount "A correct guess creates a third transaction." 3
              balance2 <- valueAt address
              liftIO $
                  assertEqual
                      "The wallet should now have its money back."
                      (lovelaceValueOf openingBalance)
                      balance2
              chainOverview <- runGlobalQuery (chainOverviewProjection @TestContracts)
              liftIO $ do
                  annotatedBlockchain <-
                      doAnnotateBlockchain
                          (chainOverviewBlockchain chainOverview)
                  let allDereferencedInputs :: [DereferencedInput]
                      allDereferencedInputs =
                          mconcat $
                          dereferencedInputs <$> mconcat annotatedBlockchain
                  assertBool
                      "Full TX history can be annotated."
                      (all isFound allDereferencedInputs)
        ]

assertTxCount ::
    ( Member (EventLogEffect (ChainEvent TestContracts)) effs
    , LastMember m effs
    , MonadIO m)
    => String
    -> Int
    -> Eff effs ()
assertTxCount msg expected = do
    txs <- runGlobalQuery (txHistoryProjection @TestContracts)
    liftIO $ assertEqual msg expected $ length txs

type SpecEffects =
        '[Error WalletAPIError
        , Error SCBError
        , EventLogEffect (ChainEvent TestContracts)
        , Log
        , ContractEffect TestContracts
        , NodeFollowerEffect
        , EmulatorLog.Log
        ]

lock ::
    ( Members SCBClientEffects effs
    )
    => UUID
    -> Contracts.Game.LockParams
    -> Eff effs ()
lock uuid params =
    updateContract @TestContracts uuid "lock" (toJSON params)

guess ::
    ( Members SpecEffects effs
    , Members WalletEffects effs
    )
    => UUID
    -> Contracts.Game.GuessParams
    -> Eff effs ()
guess uuid params =
    updateContract @TestContracts uuid "guess" (toJSON params)
