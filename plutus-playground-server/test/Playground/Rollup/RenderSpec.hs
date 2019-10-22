{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Playground.Rollup.RenderSpec
    ( tests
    ) where

import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.ByteString.Lazy         (ByteString)
import qualified Data.ByteString.Lazy         as LBS
import           Data.Text.Encoding           (encodeUtf8)
import qualified Data.Text.Lazy               as TL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (InterpreterResult (InterpreterResult, result), SourceCode (SourceCode))
import qualified Ledger.Ada                   as Ada
import           Ledger.Value                 (Value)
import qualified Ledger.Value                 as Value
import qualified Playground.Interpreter       as PI
import           Playground.Types             (EndpointName (EndpointName),
                                               Evaluation (Evaluation, program, sourceCode, wallets),
                                               EvaluationResult (resultBlockchain, walletKeys),
                                               Expression (AddBlocks, CallEndpoint, arguments, blocks, endpointName, wallet),
                                               SimulatorWallet (SimulatorWallet), simulatorWalletBalance,
                                               simulatorWalletWallet)
import           Playground.Usecases          (crowdfunding, vesting)
import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.Golden            (goldenVsString)
import           Test.Tasty.HUnit             (assertFailure)
import           Wallet.Emulator.Types        (Wallet (Wallet), walletPubKey)
import           Wallet.Rollup.Render         (showBlockchain)

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
            { sourceCode = SourceCode vesting
            , wallets =
                  [ mkSimulatorWallet w1 initialBalance
                  , mkSimulatorWallet w1 initialBalance
                  ]
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "vest funds"
                            , wallet = w2
                            , arguments = toEndpointParam ()
                            }
                      ]
            }

crowdfundingEval :: Evaluation
crowdfundingEval =
    Evaluation
        { wallets =
              [ mkSimulatorWallet w1 initialBalance
              , mkSimulatorWallet w2 initialBalance
              , mkSimulatorWallet w3 initialBalance
              ]
        , program =
              toJSONString
                  [ CallEndpoint
                        { endpointName = EndpointName "schedule collection"
                        , wallet = w1
                        , arguments = toEndpointParam ()
                        }
                  , CallEndpoint
                        { endpointName = EndpointName "contribute"
                        , wallet = w2
                        , arguments =
                              toEndpointParam $
                              JSON.object
                                  [ ( "contributor"
                                    , JSON.toJSON $ walletPubKey w2)
                                  , ( "contribValue"
                                    , JSON.toJSON $ Ada.lovelaceValueOf 8)
                                  ]
                        }
                  , CallEndpoint
                        { endpointName = EndpointName "contribute"
                        , wallet = w3
                        , arguments =
                              toEndpointParam $
                              JSON.object
                                  [ ( "contributor"
                                    , JSON.toJSON $ walletPubKey w3)
                                  , ( "contribValue"
                                    , JSON.toJSON $ Ada.lovelaceValueOf 8)
                                  ]
                        }
                  , AddBlocks {blocks = 10}
                  ]
        , sourceCode = SourceCode crowdfunding
        }
  where
    initialBalance =
        Ada.adaValueOf 10 <> Value.singleton "b0b0" "USDToken" 20 <>
        Value.singleton "b0b0" "EURToken" 30

w1, w2, w3 :: Wallet
w1 = Wallet 1

w2 = Wallet 2

w3 = Wallet 3

mkSimulatorWallet :: Wallet -> Value -> SimulatorWallet
mkSimulatorWallet simulatorWalletWallet simulatorWalletBalance =
    SimulatorWallet {..}

------------------------------------------------------------
render :: Evaluation -> IO ByteString
render scenario = do
    result <- runExceptT $ PI.runFunction maxInterpretationTime scenario
    case result of
        Left err -> assertFailure $ show err
        Right InterpreterResult {result = evaluationResult} ->
            case showBlockchain
                     (walletKeys evaluationResult)
                     (resultBlockchain evaluationResult) of
                Left err       -> assertFailure $ show err
                Right rendered -> pure . LBS.fromStrict . encodeUtf8 $ rendered
  where
    maxInterpretationTime :: Microsecond
    maxInterpretationTime = fromMicroseconds 100 * 1000 * 1000

-- | Encode a value in JSON, then make a JSON *string* from that
toJSONString :: JSON.ToJSON a => a -> JSON.Value
toJSONString = JSON.String . TL.toStrict . JSON.encodeToLazyText

toEndpointParam :: JSON.ToJSON a => a -> JSON.Value
toEndpointParam arg = toJSONString [arg]
