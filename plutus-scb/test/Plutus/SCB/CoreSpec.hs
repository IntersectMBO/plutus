{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Cardano.Node.Follower                         (NodeFollowerEffect)
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
import           Plutus.SCB.Effects.EventLog                   (EventLogEffect)
import           Plutus.SCB.Events                             (ChainEvent)
import           Plutus.SCB.TestApp                            (runScenario, sync, valueAt)
import           Plutus.SCB.Types                              (SCBError)
import           Test.QuickCheck.Instances.UUID                ()
import           Test.Tasty                                    (TestTree, testGroup)
import           Test.Tasty.HUnit                              (HasCallStack, assertEqual, testCase)
import           Wallet.API                                    (ChainIndexEffect, NodeClientEffect,
                                                                SigningProcessEffect, WalletAPIError, WalletEffect,
                                                                ownPubKey)
import           Wallet.Effects                                (WalletEffects)
import qualified Wallet.Emulator.Chain                         as Chain
import           Wallet.Emulator.ChainIndex                    (ChainIndexControlEffect)
import           Wallet.Emulator.NodeClient                    (NodeControlEffect)
import           Wallet.Emulator.SigningProcess                (SigningProcessControlEffect)

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
        [ testCase "Guessing Game" $
          runScenario $ do
              let openingBalance = 10000
                  lockAmount = 15
              address <- pubKeyAddress <$> ownPubKey
              balance0 <- valueAt address
              liftIO $
                  assertEqual
                      "Check our opening balance."
                      (lovelaceValueOf openingBalance)
                      balance0
              installContract "game"
              -- need to add contract address to wallet's watched addresses
              uuid <- activateContract "game"
              sync
              assertTxCount
                  "Activating the game does not generate transactions."
                  0
              lock
                  uuid
                  Contracts.Game.LockParams
                      { Contracts.Game.amount = lovelaceValueOf lockAmount
                      , Contracts.Game.secretWord = "password"
                      }
              Chain.processBlock
              sync
              assertTxCount "Locking the game should produce one transaction" 1
              balance1 <- valueAt address
              liftIO $
                  assertEqual
                      "Locking the game should reduce our balance."
                      (lovelaceValueOf (openingBalance - lockAmount))
                      balance1
              guess
                  uuid
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "wrong"}
              Chain.processBlock
              sync
              assertTxCount "A wrong guess still produces a transaction." 2
              guess
                  uuid
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "password"}
              Chain.processBlock
              sync
              assertTxCount "A correct guess creates a third transaction." 3
              balance2 <- valueAt address
              liftIO $
                  assertEqual
                      "The wallet should now have its money back."
                      (lovelaceValueOf openingBalance)
                      balance2
        ]

assertTxCount ::
    ( Member (EventLogEffect ChainEvent) effs
    , LastMember m effs
    , MonadIO m)
    => String
    -> Int
    -> Eff effs ()
assertTxCount msg expected = do
    txs <- runGlobalQuery txHistoryProjection
    liftIO $ assertEqual msg expected $ length txs

type SpecEffects =
        '[Error WalletAPIError
        , Error SCBError
        , EventLogEffect ChainEvent
        , NodeControlEffect
        , ChainIndexControlEffect
        , SigningProcessControlEffect
        , Log
        , ContractEffect
        , NodeFollowerEffect
        , EmulatorLog.Log
        ]

lock ::
    ( Members SpecEffects effs
    , Members WalletEffects effs
    )
    => UUID
    -> Contracts.Game.LockParams
    -> Eff effs ()
lock uuid params =
    updateContract uuid "lock" (toJSON params)

guess ::
    ( Members SpecEffects effs
    , Members WalletEffects effs
    )
    => UUID
    -> Contracts.Game.GuessParams
    -> Eff effs ()
guess uuid params =
    updateContract uuid "guess" (toJSON params)
