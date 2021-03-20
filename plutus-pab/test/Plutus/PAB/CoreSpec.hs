{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Plutus.PAB.CoreSpec
    ( tests
    ) where

import           Control.Lens                                      ((&), (+~))
import           Control.Monad                                     (unless, void)
import           Control.Monad.Freer                               (Eff, Member, Members)
import           Control.Monad.Freer.Error                         (Error, throwError)
import           Control.Monad.Freer.Extras.Log                    (LogMsg)
import qualified Control.Monad.Freer.Extras.Log                    as EmulatorLog
import           Control.Monad.Freer.Extras.State                  (use)
import           Control.Monad.Freer.State                         (State)
import qualified Data.Aeson                                        as JSON
import           Data.Foldable                                     (fold)

import qualified Data.Aeson.Types                                  as JSON
import           Data.Either                                       (isRight)
import qualified Data.Map                                          as Map
import           Data.Semigroup                                    (Last (..))
import qualified Data.Set                                          as Set
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Extras                                  (tshow)
import           Plutus.Contracts.Currency (Currency, SimpleMPS (..))
import qualified Plutus.Contracts.Game     as Contracts.Game
import           Ledger                                            (pubKeyAddress)
import           Ledger.Ada                                        (lovelaceValueOf)
import           Plutus.PAB.Command                                ()
import           Plutus.PAB.Core
import           Plutus.PAB.Core.ContractInstance                  (ContractInstanceMsg)
import qualified Plutus.PAB.Db.Eventful.Query                      as Query
import           Plutus.PAB.Effects.Contract                       (ContractEffect)
import           Plutus.PAB.Effects.Contract.ContractTest          (TestContracts (..))
import           Plutus.PAB.Effects.EventLog                       (EventLogEffect)
import           Plutus.PAB.Events.ContractInstanceState           (PartiallyDecodedResponse (..))
import           Plutus.PAB.Simulator                              (Simulation, TxCounts (..))
import qualified Plutus.PAB.Simulator                              as Simulator
import           Plutus.PAB.Types                                  (PABError (..), chainOverviewBlockchain,
                                                                    mkChainOverview)
import           Test.QuickCheck.Instances.UUID                    ()
import           Test.Tasty                                        (TestTree, testGroup)
import           Test.Tasty.HUnit                                  (testCase)
import           Wallet.API                                        (WalletAPIError, ownPubKey)
import qualified Wallet.Emulator.Chain                             as Chain
import           Wallet.Emulator.Wallet                            (Wallet (..))
import           Wallet.Rollup                                     (doAnnotateBlockchain)
import           Wallet.Rollup.Types                               (DereferencedInput, dereferencedInputs, isFound)
import           Wallet.Types                                      (ContractInstanceId)

tests :: TestTree
tests = testGroup "Plutus.PAB.Core" [installContractTests, executionTests]

runScenario :: Simulation TestContracts a -> IO ()
runScenario sim = do
    result <- Simulator.runSimulation sim
    case result of
        Left err -> error (show err)
        Right _  -> pure ()

defaultWallet :: Wallet
defaultWallet = Wallet 1

installContractTests :: TestTree
installContractTests =
    testGroup
        "installContract scenario"
        [ testCase "Initially there are no contracts active" $
            runScenario $ do
                active <- Simulator.activeContracts
                assertEqual "" 0 $ Set.size active
        , testCase "We can activate a contract" $
          runScenario $ do
              void $ Simulator.activateContract defaultWallet Game
              --
              active <- Simulator.activeContracts
              assertEqual "" 1 $ Set.size active
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
    let mps = SimpleMPS{tokenName="my token", amount = 10000}
        getCurrency :: JSON.Value -> Maybe Currency
        getCurrency vl = do
            case JSON.parseEither JSON.parseJSON vl of
                Right (Just (Last cur)) -> Just cur
                _                       -> Nothing
    in
    testCase "Currency" $
        runScenario $ do
              initialTxCounts <- Simulator.txCounts
              instanceId <- Simulator.activateContract defaultWallet Currency
              assertTxCounts
                  "Activating the currency contract does not generate transactions."
                  initialTxCounts
              createCurrency instanceId mps
              result <- Simulator.waitForState getCurrency instanceId
              assertTxCounts
                "Forging the currency should produce two valid transactions."
                (initialTxCounts & Simulator.txValidated +~ 2)

rpcTest :: TestTree
rpcTest =
    testCase "RPC" $
        runScenario $ do
            clientId <- Simulator.activateContract defaultWallet RPCClient
            serverId <- Simulator.activateContract defaultWallet RPCServer
            Simulator.waitNSlots 1
            void $ Simulator.callEndpointOnInstance serverId "serve" ()
            Simulator.waitNSlots 1
            callAdder clientId serverId
            Simulator.waitNSlots 5
            assertDone defaultWallet clientId
            assertDone defaultWallet serverId

guessingGameTest :: TestTree
guessingGameTest =
    testCase "Guessing Game" $
          runScenario $ do
              let openingBalance = 100000000
                  lockAmount = 15
              address <- pubKeyAddress <$> Simulator.handleAgentThread defaultWallet ownPubKey
              balance0 <- Simulator.valueAt address
              initialTxCounts <- Simulator.txCounts
              assertEqual
                    "Check our opening balance."
                    (lovelaceValueOf openingBalance)
                    balance0
              -- need to add contract address to wallet's watched addresses
              instanceId <- Simulator.activateContract defaultWallet Game

              assertTxCounts
                  "Activating the game does not generate transactions."
                  initialTxCounts
              _ <- Simulator.waitNSlots 2
              lock
                  instanceId
                  Contracts.Game.LockParams
                      { Contracts.Game.amount = lovelaceValueOf lockAmount
                      , Contracts.Game.secretWord = "password"
                      }
              _ <- Simulator.waitNSlots 2
              assertTxCounts
                  "Locking the game should produce one transaction"
                  (initialTxCounts & Simulator.txValidated +~ 1)
              balance1 <- Simulator.valueAt address
              assertEqual
                  "Locking the game should reduce our balance."
                  (lovelaceValueOf (openingBalance - lockAmount))
                  balance1
              game1Id <- Simulator.activateContract defaultWallet Game

              guess
                  game1Id
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "wrong"}

              _ <- Simulator.waitNSlots 2
              assertTxCounts
                "A wrong guess does not produce a valid transaction on the chain."
                (initialTxCounts & Simulator.txValidated +~ 1)
              game2Id <- Simulator.activateContract defaultWallet Game

              _ <- Simulator.waitNSlots 2
              guess
                  game2Id
                  Contracts.Game.GuessParams
                      {Contracts.Game.guessWord = "password"}

              _ <- Simulator.waitNSlots 2
              assertTxCounts
                "A correct guess creates a second transaction."
                (initialTxCounts & Simulator.txValidated +~ 2)
              balance2 <- Simulator.valueAt address
              assertEqual
                "The wallet should now have its money back."
                (lovelaceValueOf openingBalance)
                balance2
              blocks <- Simulator.blockchain
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
    Text
    -> TxCounts
    -> Simulation TestContracts ()
assertTxCounts msg expected = Simulator.txCounts >>= assertEqual msg expected

assertDone ::
    Wallet
    -> ContractInstanceId
    -> Simulation TestContracts ()
assertDone wallet i = do
    PartiallyDecodedResponse{hooks} <- Simulator.instanceState wallet i
    case hooks of
        [] -> pure ()
        xs ->
            throwError
                $ OtherError
                $ Text.unwords
                    [ "Contract"
                    , tshow i
                    , "not done. Open requests:"
                    , tshow xs
                    ]

lock ::
    ContractInstanceId
    -> Contracts.Game.LockParams
    -> Simulation TestContracts ()
lock uuid params = do
    let ep = "lock"
    _ <- Simulator.waitForEndpoint uuid ep
    void $ Simulator.callEndpointOnInstance uuid ep params

guess ::
    ContractInstanceId
    -> Contracts.Game.GuessParams
    -> Simulation TestContracts ()
guess uuid params = do
    let ep = "guess"
    _ <- Simulator.waitForEndpoint uuid ep
    void $ Simulator.callEndpointOnInstance uuid ep params

callAdder ::
    ContractInstanceId
    -> ContractInstanceId
    -> Simulation TestContracts ()
callAdder source target = do
    let ep = "target instance"
    _ <- Simulator.waitForEndpoint source ep
    void $ Simulator.callEndpointOnInstance source ep target

-- | Call the @"Create native token"@ endpoint on the currency contract.
createCurrency ::
    ContractInstanceId
    -> SimpleMPS
    -> Simulation TestContracts ()
createCurrency uuid value = do
    let ep = "Create native token"
    _ <- Simulator.waitForEndpoint uuid ep
    void $ Simulator.callEndpointOnInstance uuid ep value

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
