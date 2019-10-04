{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Playground.Rollup.RenderSpec
    ( tests
    ) where

import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.Aeson.Types             (object, (.=))
import           Data.ByteString.Lazy         (ByteString)
import qualified Data.ByteString.Lazy         as LBS
import           Data.Text.Encoding           (encodeUtf8)
import qualified Data.Text.Lazy               as TL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (SourceCode (SourceCode))
import qualified Ledger.Ada                   as Ada
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import qualified Playground.Interpreter       as PI
import           Playground.Rollup.Render     (showBlockchain)
import           Playground.Server            (postProcessEvaluation)
import           Playground.Types             (Evaluation (Evaluation), Expression (Action, Wait), Fn (Fn),
                                               SimulatorWallet (SimulatorWallet), simulatorWalletBalance,
                                               simulatorWalletWallet)
import           Playground.Usecases          (crowdfunding, vesting)
import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.Golden            (goldenVsString)
import           Test.Tasty.HUnit             (assertFailure)
import           Wallet.Emulator.Types        (Wallet (Wallet))

tests :: TestTree
tests = testGroup "Playground.Rollup.Render" [showBlockchainTest]

showBlockchainTest :: TestTree
showBlockchainTest =
    testGroup
        "showBlockchain"
        [ goldenVsString
              "renders a vest-funds scenario sensibly"
              "test/Playground/Rollup/renderVestFunds.txt"
              (render vestFundsEval)
        , goldenVsString
              "renders a crowdfunding scenario sensibly"
              "test/Playground/Rollup/renderCrowdfunding.txt"
              (render crowdfundingEval)
        ]
  where
    initialBalance = Ada.adaValueOf 10
    vestFundsEval =
        Evaluation
            [mkSimulatorWallet w1 initialBalance]
            [ Action
                  (Fn "vestFunds")
                  w1
                  [theVestingTranche, theVestingTranche, theVestingOwner]
            ]
            (SourceCode vesting)
            []
    theVestingTranche =
        toJSONString $
        object
            [ "vestingTrancheDate" .= object ["getSlot" .= mkI 1]
            , "vestingTrancheAmount" .= JSON.toJSON (Ada.adaValueOf 1)
            ]
    theVestingOwner = toJSONString $ JSON.toJSON w1

crowdfundingEval :: Evaluation
crowdfundingEval =
    Evaluation
        [ mkSimulatorWallet w1 initialBalance
        , mkSimulatorWallet w2 initialBalance
        , mkSimulatorWallet w3 initialBalance
        ]
        [ Action
              (Fn "scheduleCollection")
              w1
              [theDeadline, theTarget, theCollectionDeadline, theWallet]
        , Action
              (Fn "contribute")
              w2
              [ theDeadline
              , theTarget
              , theCollectionDeadline
              , theWallet
              , theContribution
              ]
        , Action
              (Fn "contribute")
              w3
              [ theDeadline
              , theTarget
              , theCollectionDeadline
              , theWallet
              , theContribution
              ]
        , Wait 10
        ]
        (SourceCode crowdfunding)
        []
  where
    initialBalance =
        Ada.adaValueOf 10 <> Value.singleton "b0b0" "USDToken" 20 <>
        Value.singleton "b0b0" "EURToken" 30
    theDeadline = toJSONString (object ["getSlot" .= mkI 10])
    theTarget = toJSONString (Ada.adaValueOf 10)
    theCollectionDeadline = toJSONString (object ["getSlot" .= mkI 20])
    theWallet = toJSONString w1
    theContribution = toJSONString $ Ada.adaValueOf 8

w1, w2, w3 :: Wallet
w1 = Wallet 1

w2 = Wallet 2

w3 = Wallet 3

mkSimulatorWallet :: Wallet -> Value -> SimulatorWallet
mkSimulatorWallet simulatorWalletWallet simulatorWalletBalance =
    SimulatorWallet {..}

mkI :: Int -> JSON.Value
mkI = JSON.toJSON

-- | Encode a value in JSON, then make a JSON *string* from that
toJSONString :: JSON.ToJSON a => a -> JSON.Value
toJSONString = JSON.String . TL.toStrict . JSON.encodeToLazyText

------------------------------------------------------------
render :: Evaluation -> IO ByteString
render scenario = do
    result <- runExceptT $ PI.runFunction maxInterpretationTime scenario
    case postProcessEvaluation result of
        Left err -> assertFailure $ show err
        Right evaluationResult ->
            case showBlockchain evaluationResult of
                Left err       -> assertFailure $ show err
                Right rendered -> pure . LBS.fromStrict . encodeUtf8 $ rendered
  where
    maxInterpretationTime :: Microsecond
    maxInterpretationTime = fromMicroseconds 100 * 1000 * 1000
