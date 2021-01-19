{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Plutus.PAB.CoreSpec
    ( tests
    ) where

import           Cardano.Node.Follower                             (NodeFollowerEffect)
import           Control.Lens                                      ((&), (+~))
import           Control.Monad                                     (unless, void)
import           Control.Monad.Freer                               (Eff, Member, Members)
import           Control.Monad.Freer.Error                         (Error, throwError)
import           Control.Monad.Freer.Extra.Log                     (LogMsg)
import           Control.Monad.Freer.Extra.State                   (use)
import qualified Control.Monad.Freer.Log                           as EmulatorLog
import           Control.Monad.Freer.State                         (State)
import           Data.Foldable                                     (fold)
import qualified Data.Map                                          as Map
import qualified Data.Set                                          as Set
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Language.PlutusTx.Coordination.Contracts.Currency (SimpleMPS (..))
import qualified Language.PlutusTx.Coordination.Contracts.Game     as Contracts.Game
import           Ledger                                            (pubKeyAddress)
import           Ledger.Ada                                        (lovelaceValueOf)
import           Plutus.PAB.Command                                ()
import           Plutus.PAB.Core
import           Plutus.PAB.Core.ContractInstance                  (ContractInstanceMsg)
import           Plutus.PAB.Effects.Contract                       (ContractEffect)
import           Plutus.PAB.Effects.ContractTest                   (TestContracts (..))
import           Plutus.PAB.Effects.EventLog                       (EventLogEffect)
import           Plutus.PAB.Effects.MultiAgent                     (PABClientEffects, agentAction)
import           Plutus.PAB.Events                                 (ChainEvent, ContractInstanceId,
                                                                    ContractInstanceState (..), hooks)
import           Plutus.PAB.MockApp                                (TestState, TxCounts (..), blockchainNewestFirst,
                                                                    defaultWallet, runScenario, syncAll, txCounts,
                                                                    txValidated, valueAt)
import qualified Plutus.PAB.Query                                  as Query
import           Plutus.PAB.Types                                  (PABError (..), chainOverviewBlockchain,
                                                                    mkChainOverview)
import           Plutus.PAB.Utils                                  (tshow)
import           Test.QuickCheck.Instances.UUID                    ()
import           Test.Tasty                                        (TestTree, testGroup)
import           Test.Tasty.HUnit                                  (testCase)
import           Wallet.API                                        (WalletAPIError, ownPubKey)
import qualified Wallet.Emulator.Chain                             as Chain
import           Wallet.Rollup                                     (doAnnotateBlockchain)
import           Wallet.Rollup.Types                               (DereferencedInput, dereferencedInputs, isFound)

tests :: TestTree
tests = testGroup "Plutus.PAB.Core" [installContractTests, executionTests]

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
        [ guessingGameTest
        , currencyTest
        , rpcTest
        ]

currencyTest :: TestTree
currencyTest =
    let mps = SimpleMPS{tokenName="my token", amount = 10000} in
    testCase "Currency" $
        runScenario $ do
              initialTxCounts <- txCounts
              agentAction defaultWallet (installContract Currency)
              contractState <- agentAction defaultWallet (activateContract Currency)
              let instanceId = csContract contractState
              syncAll
              assertTxCounts
                  "Activating the currency contract does not generate transactions."
                  initialTxCounts
              agentAction defaultWallet $ createCurrency instanceId mps
              syncAll
              void Chain.processBlock
              syncAll
              void Chain.processBlock
              syncAll
              assertTxCounts
                "Forging the currency should produce two valid transactions."
                (initialTxCounts & txValidated +~ 2)

rpcTest :: TestTree
rpcTest =
    testCase "RPC" $
        runScenario $ do
            agentAction defaultWallet (installContract RPCClient)
            agentAction defaultWallet (installContract RPCServer)
            ContractInstanceState{csContract=clientId} <- agentAction defaultWallet (activateContract RPCClient)
            ContractInstanceState{csContract=serverId} <- agentAction defaultWallet (activateContract RPCServer)
            syncAll
            agentAction defaultWallet $ void $ callContractEndpoint @TestContracts serverId "serve" ()
            syncAll
            agentAction defaultWallet $ callAdder clientId serverId
            syncAll
            syncAll
            syncAll
            agentAction defaultWallet $ do
                assertDone clientId
                assertDone serverId

guessingGameTest :: TestTree
guessingGameTest =
    testCase "Guessing Game" $
          runScenario $ do
              let openingBalance = 100000000
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
              contractState <- agentAction defaultWallet (activateContract Game)
              let instanceId = csContract contractState
              syncAll
              assertTxCounts
                  "Activating the game does not generate transactions."
                  initialTxCounts
              agentAction defaultWallet $ lock
                  instanceId
                  Contracts.Game.LockParams
                      { Contracts.Game.amount = lovelaceValueOf lockAmount
                      , Contracts.Game.secretWord = "password"
                      }
              syncAll
              void Chain.processBlock
              syncAll
              assertTxCounts
                  "Locking the game should produce one transaction"
                  (initialTxCounts & txValidated +~ 1)
              balance1 <- valueAt address
              assertEqual
                  "Locking the game should reduce our balance."
                  (lovelaceValueOf (openingBalance - lockAmount))
                  balance1

              game1State <- agentAction defaultWallet (activateContract Game)
              syncAll
              agentAction defaultWallet $ guess
                  (csContract game1State)
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "wrong"}
              syncAll
              void Chain.processBlock
              assertTxCounts
                "A wrong guess still produces a transaction."
                (initialTxCounts & txValidated +~ 2)
              game2State <- agentAction defaultWallet (activateContract Game)
              syncAll
              agentAction defaultWallet $ guess
                  (csContract game2State)
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "password"}
              syncAll
              void Chain.processBlock
              assertTxCounts
                "A correct guess creates a third transaction."
                (initialTxCounts & txValidated +~ 3)
              balance2 <- valueAt address
              assertEqual
                "The wallet should now have its money back."
                (lovelaceValueOf openingBalance)
                balance2
              blocks <- use blockchainNewestFirst
              assertBool
                  "We have some confirmed blocks in this test."
                  (not (null (mconcat blocks)))
              let chainOverview = mkChainOverview (reverse blocks)
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
    , Member (Error PABError) effs
    )
    => Text
    -> TxCounts
    -> Eff effs ()
assertTxCounts msg expected =  txCounts >>= assertEqual msg expected

assertDone ::
    ( Member (EventLogEffect (ChainEvent TestContracts)) effs
    , Member (Error PABError) effs
    )
    => ContractInstanceId
    -> Eff effs ()
assertDone i = do
    h <- fmap (hooks . csCurrentState) <$> runGlobalQuery (Query.contractState @TestContracts)
    case Map.lookup i h of
        Just [] -> pure ()
        Just xs ->
            throwError
                $ OtherError
                $ Text.unwords
                    [ "Contract"
                    , tshow i
                    , "not done. Open requests:"
                    , tshow xs
                    ]
        Nothing -> throwError $ ContractInstanceNotFound i

type SpecEffects =
        '[Error WalletAPIError
        , Error PABError
        , EventLogEffect (ChainEvent TestContracts)
        , ContractEffect TestContracts
        , NodeFollowerEffect
        , LogMsg Text
        , LogMsg (ContractInstanceMsg TestContracts)
        , EmulatorLog.LogObserve (EmulatorLog.LogMessage Text)
        ]

lock ::
    ( Members PABClientEffects effs
    )
    => ContractInstanceId
    -> Contracts.Game.LockParams
    -> Eff effs ()
lock uuid params =
    void $ callContractEndpoint @TestContracts uuid "lock" params

guess ::
    Members SpecEffects effs
    => ContractInstanceId
    -> Contracts.Game.GuessParams
    -> Eff effs ()
guess uuid params =
    void $ callContractEndpoint @TestContracts uuid "guess" params

callAdder ::
    Members SpecEffects effs
    => ContractInstanceId
    -> ContractInstanceId
    -> Eff effs ()
callAdder source target =
    void $ callContractEndpoint @TestContracts source "target instance" target

-- | Call the @"Create native token"@ endpoint on the currency contract.
createCurrency ::
    Members SpecEffects effs
    => ContractInstanceId
    -> SimpleMPS
    -> Eff effs ()
createCurrency uuid value =
    void $ callContractEndpoint @TestContracts uuid "Create native token" value

assertEqual ::
    forall a effs.
    ( Eq a
    , Show a
    , Member (Error PABError) effs
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
            , "Actual: " <> tshow actual
            ]

assertBool ::
    forall effs.
    ( Member (Error PABError) effs
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
