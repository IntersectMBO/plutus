{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

module Plutus.SCB.CoreSpec
    ( tests
    ) where

import           Cardano.Node.Follower                             (NodeFollowerEffect)
import           Control.Lens
import           Control.Monad                                     (unless, void)
import           Control.Monad.Freer                               (Eff, LastMember, Member, Members)
import           Control.Monad.Freer.Error                         (Error, throwError)
import           Control.Monad.Freer.Extra.Log                     (Log)
import qualified Control.Monad.Freer.Log                           as EmulatorLog
import           Control.Monad.Freer.State                         (State)
import           Control.Monad.IO.Class                            (MonadIO, liftIO)
import           Data.Aeson                                        as JSON
import           Data.Foldable                                     (fold)
import qualified Data.Set                                          as Set
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Eventful                                          (UUID, globalStreamProjection, streamProjectionState)
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Contracts.Currency
import qualified Language.PlutusTx.Coordination.Contracts.Game     as Contracts.Game
import           Ledger                                            (pubKeyAddress)
import           Ledger.Ada                                        (lovelaceValueOf)
import           Plutus.SCB.Command                                ()
import           Plutus.SCB.Core
import           Plutus.SCB.Effects.Contract                       (ContractEffect)
import           Plutus.SCB.Effects.ContractTest                   (TestContracts (..))
import           Plutus.SCB.Effects.EventLog                       (EventLogEffect)
import           Plutus.SCB.Effects.MultiAgent                     (SCBClientEffects, agentAction, agentControlAction)
import           Plutus.SCB.Events                                 (ChainEvent, ContractInstanceId)
import           Plutus.SCB.Query                                  (chainOverviewProjection, txHistoryProjection)
import           Plutus.SCB.TestApp                                (TestState, TxCounts (..), defaultWallet,
                                                                    runScenario, sync, syncAll, txCounts, txValidated,
                                                                    valueAt)
import           Plutus.SCB.Types                                  (SCBError (..), chainOverviewBlockchain)
import           Plutus.SCB.Utils                                  (tshow)
import           Test.QuickCheck.Instances.UUID                    ()
import           Test.Tasty                                        (TestTree, testGroup)
import           Test.Tasty.HUnit                                  (HasCallStack, testCase)
import           Wallet.API                                        (ChainIndexEffect, NodeClientEffect,
                                                                    SigningProcessEffect, WalletAPIError, WalletEffect,
                                                                    ownPubKey)
import           Wallet.Effects                                    (WalletEffects)
import qualified Wallet.Emulator.Chain                             as Chain
import           Wallet.Emulator.ChainIndex                        (ChainIndexControlEffect)
import           Wallet.Emulator.NodeClient                        (NodeControlEffect)
import           Wallet.Emulator.SigningProcess                    (SigningProcessControlEffect)
import           Wallet.Emulator.Wallet                            (Wallet (..))
import           Wallet.Rollup                                     (doAnnotateBlockchain)
import           Wallet.Rollup.Types                               (DereferencedInput (DereferencedInput, InputNotFound),
                                                                    dereferencedInputs, isFound)

tests :: TestTree
tests = testGroup "SCB.Core" [installContractTests, executionTests]

installContractTests :: TestTree
installContractTests =
    testGroup
        "installContract scenario"
        [ testCase "Initially there are no contracts installed" $
          runScenario $ do
              installed <- agentAction defaultWallet (installedContracts @TestContracts)
              assertEqual "" 0 $ Set.size installed
        , testCase "Initially there are no contracts active" $
          runScenario $ do
              active <- agentAction defaultWallet (activeContracts @TestContracts)
              assertEqual "" 0 $ Set.size $ fold active
        , testCase
              "Installing a contract successfully increases the installed contract count" $
          runScenario $ agentAction defaultWallet $ do
              installContract @TestContracts Game
              --
              installed <- installedContracts @TestContracts
              assertEqual "" 1 $ Set.size installed
              --
              active <- activeContracts @TestContracts
              assertEqual "" 0 $ Set.size $ fold active
        , testCase "We can activate a contract" $
          runScenario $ agentAction defaultWallet $ do
              installContract Game
              --
              installed <- installedContracts @TestContracts
              assertEqual "" 1 $ Set.size installed
              --
              void $ activateContract Game
              --
              active <- activeContracts @TestContracts
              assertEqual "" 1 $ Set.size $ fold active
        ]

executionTests :: TestTree
executionTests =
    testGroup
        "Executing contracts."
        [ guessingGameTest ]

guessingGameTest =
    testCase "Guessing Game" $
          runScenario $ do
              let openingBalance = 10000
                  lockAmount = 15
              address <- pubKeyAddress <$> agentAction defaultWallet ownPubKey
              balance0 <- valueAt address
              initialTxCounts <- txCounts
              assertEqual
                    "Check our opening balance."
                    (lovelaceValueOf openingBalance)
                    balance0
              agentAction defaultWallet (installContract Game)
              -- need to add contract address to wallet's watched addresses
              uuid <- agentAction defaultWallet (activateContract Game)
              syncAll
              assertTxCounts
                  "Activating the game does not generate transactions."
                  initialTxCounts
              agentAction defaultWallet $ lock
                  uuid
                  Contracts.Game.LockParams
                      { Contracts.Game.amount = lovelaceValueOf lockAmount
                      , Contracts.Game.secretWord = "password"
                      }
              syncAll
              Chain.processBlock
              syncAll
              assertTxCounts
                  "Locking the game should produce one transaction"
                  (initialTxCounts & txValidated +~ 1)
              balance1 <- valueAt address
              assertEqual
                  "Locking the game should reduce our balance."
                  (lovelaceValueOf (openingBalance - lockAmount))
                  balance1

              newUUID <- agentAction defaultWallet (activateContract Game)
              syncAll
              agentAction defaultWallet $ guess
                  newUUID
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "wrong"}
              syncAll
              syncAll
              Chain.processBlock
              assertTxCounts
                "A wrong guess still produces a transaction."
                (initialTxCounts & txValidated +~ 2)
              newUUID2 <- agentAction defaultWallet (activateContract Game)
              syncAll
              agentAction defaultWallet $ guess
                  newUUID2
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "password"}
              syncAll
              syncAll
              Chain.processBlock
              assertTxCounts
                "A correct guess creates a third transaction."
                (initialTxCounts & txValidated +~ 3)
              balance2 <- valueAt address
              assertEqual
                "The wallet should now have its money back."
                (lovelaceValueOf openingBalance)
                balance2
              chainOverview <- agentAction defaultWallet $ runGlobalQuery (chainOverviewProjection @TestContracts)
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

assertTxCounts ::
    ( Member (State TestState) effs
    , Member (Error SCBError) effs
    )
    => Text
    -> TxCounts
    -> Eff effs ()
assertTxCounts msg expected =  txCounts >>= assertEqual msg expected

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
    => ContractInstanceId
    -> Contracts.Game.LockParams
    -> Eff effs ()
lock uuid params =
    void $ callContractEndpoint @TestContracts uuid "lock" params

guess ::
    ( Members SpecEffects effs
    , Members WalletEffects effs
    )
    => ContractInstanceId
    -> Contracts.Game.GuessParams
    -> Eff effs ()
guess uuid params =
    void $ callContractEndpoint @TestContracts uuid "guess" params

assertEqual ::
    forall a effs.
    ( Eq a
    , Show a
    , Member (Error SCBError) effs
    )
    => Text
    -> a
    -> a
    -> Eff effs ()
assertEqual msg expected actual =
    unless (expected == actual)
        $ throwError
        $ OtherError
        $ Text.unwords
            [ msg
            , "Expected: " <> tshow expected
            , "Actual:" <> tshow actual
            ]

assertBool ::
    forall a effs.
    ( Member (Error SCBError) effs
    )
    => Text
    -> Bool
    -> Eff effs ()
assertBool msg b =
    unless b
        $ throwError
        $ OtherError
        $ Text.unwords
            [ msg
            , "failed"
            ]
