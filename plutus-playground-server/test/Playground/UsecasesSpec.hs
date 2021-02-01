{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

module Playground.UsecasesSpec
    ( tests
    ) where

import           Control.Monad                                   (unless)
import           Control.Monad.Except                            (runExceptT)
import           Control.Monad.Except.Extras                     (mapError)
import           Control.Newtype.Generics                        (over)
import           Crowdfunding                                    (Contribution (Contribution), contribValue)
import           Data.Aeson                                      (ToJSON)
import qualified Data.Aeson                                      as JSON
import qualified Data.Aeson.Text                                 as JSON
import           Data.Foldable                                   (traverse_)
import           Data.List.NonEmpty                              (NonEmpty ((:|)))
import qualified Data.Text                                       as Text
import qualified Data.Text.IO                                    as Text
import qualified Data.Text.Lazy                                  as TL
import           Data.Time.Units                                 (Minute)
import           Game                                            (GuessParams (GuessParams), LockParams (LockParams),
                                                                  amount, guessWord, secretWord)
import qualified Interpreter                                     as Webghc
import           Language.Haskell.Interpreter                    (InterpreterError,
                                                                  InterpreterResult (InterpreterResult, result),
                                                                  SourceCode (SourceCode))
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (EndpointDescription))
import           Ledger.Ada                                      (adaValueOf, lovelaceValueOf)
import           Ledger.Scripts                                  (ValidatorHash (ValidatorHash))
import           Ledger.Value                                    (TokenName (TokenName), Value)
import qualified Playground.Interpreter                          as PI
import           Playground.Types                                (CompilationResult (CompilationResult),
                                                                  ContractCall (AddBlocks, AddBlocksUntil, CallEndpoint, PayToWallet),
                                                                  Evaluation (Evaluation),
                                                                  EvaluationResult (EvaluationResult), Expression,
                                                                  FunctionSchema (FunctionSchema),
                                                                  KnownCurrency (KnownCurrency),
                                                                  PlaygroundError (InterpreterError),
                                                                  SimulatorWallet (SimulatorWallet), adaCurrency,
                                                                  argument, argumentValues, caller, emulatorLog,
                                                                  endpointDescription, fundsDistribution, program,
                                                                  resultRollup, simulatorWalletBalance,
                                                                  simulatorWalletWallet, sourceCode, walletKeys,
                                                                  wallets)
import           Playground.Usecases                             (crowdFunding, errorHandling, game, vesting)
import           Schema                                          (FormSchema (FormSchemaUnit, FormSchemaValue))
import           Test.Tasty                                      (TestTree, testGroup)
import           Test.Tasty.HUnit                                (Assertion, assertEqual, assertFailure, testCase)
import           Wallet.Emulator.Types                           (Wallet (Wallet))
import           Wallet.Rollup.Render                            (showBlockchain)
import           Wallet.Rollup.Types                             (AnnotatedTx (tx))

tests :: TestTree
tests =
    testGroup
        "Playground.Usecases"
        [ vestingTest
        , gameTest
        , errorHandlingTest
        , crowdfundingTest
        , knownCurrencyTest
        ]

maxInterpretationTime :: Minute
maxInterpretationTime = 2

w1, w2, w3, w4, w5 :: Wallet
w1 = Wallet 1

w2 = Wallet 2

w3 = Wallet 3

w4 = Wallet 4

w5 = Wallet 5

mkSimulatorWallet :: Wallet -> Value -> SimulatorWallet
mkSimulatorWallet simulatorWalletWallet simulatorWalletBalance =
    SimulatorWallet {..}

vestingTest :: TestTree
vestingTest =
    testGroup
        "vesting"
        [ compilationChecks vesting
        , testCase "should compile with the expected schema" $ do
              Right (InterpreterResult _ (CompilationResult result _)) <-
                  compile vesting
              assertEqual
                  ""
                  [ FunctionSchema
                        { endpointDescription = EndpointDescription "retrieve funds"
                        , argument = FormSchemaValue
                        }
                  , FunctionSchema
                        { endpointDescription = EndpointDescription "vest funds"
                        , argument = FormSchemaUnit
                        }
                  ]
                  result
        , testCase "should run simple evaluation" $
          evaluate (mkEvaluation []) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 tenLovelace
              , mkSimulatorWallet w2 tenLovelace
              ]
        , testCase "should run simple wait evaluation" $
          evaluate (mkEvaluation [AddBlocks 10]) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 tenLovelace
              , mkSimulatorWallet w2 tenLovelace
              ]
        , testCase "should run vest funds evaluation" $
          evaluate vestFundsEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ lovelaceValueOf 10
              , mkSimulatorWallet w2 $ lovelaceValueOf 2
              ]
        , testCase "should run vest and a partial retrieve of funds" $
          evaluate vestAndPartialRetrieveEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ lovelaceValueOf 15
              , mkSimulatorWallet w2 $ lovelaceValueOf 2
              ]
        , testCase "should run vest and a full retrieve of funds" $
          evaluate vestAndFullRetrieveEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ lovelaceValueOf 18
              , mkSimulatorWallet w2 $ lovelaceValueOf 2
              ]
        ]
  where
    tenLovelace = lovelaceValueOf 10
    mkEvaluation :: [Expression] -> Evaluation
    mkEvaluation expressions =
        Evaluation
            { wallets =
                  [ mkSimulatorWallet w1 tenLovelace
                  , mkSimulatorWallet w2 tenLovelace
                  ]
            , sourceCode = vesting
            , program = toJSONString expressions
            }
    vestFundsEval = mkEvaluation [vestFunds w2, AddBlocks 1]
    vestAndPartialRetrieveEval =
        mkEvaluation
            [vestFunds w2, AddBlocks 20, retrieveFunds w1 5, AddBlocks 1]
    vestAndFullRetrieveEval =
        mkEvaluation
            [vestFunds w2, AddBlocks 40, retrieveFunds w1 8, AddBlocks 5]
    vestFunds caller = callEndpoint "vest funds" caller ()
    retrieveFunds caller balance =
        callEndpoint "retrieve funds" caller $ lovelaceValueOf balance

gameTest :: TestTree
gameTest =
    testGroup
        "game"
        [ compilationChecks game
        , testCase "should keep the funds" $
          evaluate (mkEvaluation [lock w2 "abcde" twoAda, AddBlocks 1, guess w1 "ade", AddBlocks 1]) >>=
          hasFundsDistribution
              [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 (adaValueOf 8)]
        , testCase "should unlock the funds" $
          evaluate (mkEvaluation [lock w2 "abcde" twoAda, AddBlocks 1, guess w1 "abcde", AddBlocks 1]) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 (adaValueOf 12)
              , mkSimulatorWallet w2 (adaValueOf 8)
              ]
        , testCase "Sequential fund transfer - PayToWallet" $
          evaluate (payAll w3 w4 w5) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w3 tenAda
              , mkSimulatorWallet w4 tenAda
              , mkSimulatorWallet w5 tenAda
              ]
        , testCase "Sequential fund transfer - PayToWallet" $
          evaluate (payAll w1 w2 w3) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 tenAda
              , mkSimulatorWallet w2 tenAda
              , mkSimulatorWallet w3 tenAda
              ]
        ]
  where
    tenAda = adaValueOf 10
    sourceCode = game
    wallets = [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 tenAda]
    mkEvaluation :: [Expression] -> Evaluation
    mkEvaluation expressions =
        Evaluation
            {sourceCode = game, wallets, program = toJSONString expressions}
    lock caller secretWord amount =
        callEndpoint "lock" caller $ LockParams {secretWord, amount}
    guess caller guessWord =
        callEndpoint "guess" caller $ GuessParams {guessWord}
    payAll a b c =
        Evaluation
            { sourceCode
            , wallets =
                  [ mkSimulatorWallet a tenAda
                  , mkSimulatorWallet b tenAda
                  , mkSimulatorWallet c tenAda
                  ]
            , program =
                  toJSONString
                      ([ PayToWallet a b nineAda
                       , PayToWallet b c nineAda
                       , PayToWallet c a nineAda
                       ] :: [Expression])
            }
    nineAda = adaValueOf 9
    twoAda = adaValueOf 2

hasFundsDistribution ::
       [SimulatorWallet]
    -> Either PlaygroundError (InterpreterResult EvaluationResult)
    -> Assertion
hasFundsDistribution _ (Left err) = assertFailure $ show err
hasFundsDistribution requiredDistribution (Right InterpreterResult {result = EvaluationResult {..}}) = do
    unless (requiredDistribution == fundsDistribution) $ do
        Text.putStrLn $
            either id id $ showBlockchain walletKeys $ fmap (fmap tx) resultRollup
        traverse_ print $ reverse emulatorLog
    assertEqual "" requiredDistribution fundsDistribution

errorHandlingTest :: TestTree
errorHandlingTest = testGroup "errorHandling" [compilationChecks errorHandling]

crowdfundingTest :: TestTree
crowdfundingTest =
    testGroup
        "crowdfunding"
        [ compilationChecks crowdFunding
        , testCase "should run successful campaign" $
          evaluate successfulCampaign >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ lovelaceValueOf 60
              , mkSimulatorWallet w2 $ lovelaceValueOf 19
              , mkSimulatorWallet w3 $ lovelaceValueOf 20
              , mkSimulatorWallet w4 $ lovelaceValueOf 21
              ]
        , testCase "should run failed campaign and return the funds" $
          evaluate failedCampaign >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ lovelaceValueOf 20
              , mkSimulatorWallet w2 $ lovelaceValueOf 20
              , mkSimulatorWallet w3 $ lovelaceValueOf 20
              ]
        ]
  where
    twentyLovelace = lovelaceValueOf 20
    sourceCode = crowdFunding
    successfulCampaign =
        Evaluation
            { wallets =
                  [ mkSimulatorWallet w1 $ lovelaceValueOf 30
                  , mkSimulatorWallet w2 $ lovelaceValueOf 30
                  , mkSimulatorWallet w3 $ lovelaceValueOf 30
                  , mkSimulatorWallet w4 $ lovelaceValueOf 30
                  ]
            , program =
                  toJSONString
                      [ scheduleCollection w1
                      , contribute w2 $ lovelaceValueOf 11
                      , contribute w3 $ lovelaceValueOf 10
                      , contribute w4 $ lovelaceValueOf 9
                      , AddBlocks 1
                      , AddBlocksUntil 40
                      , AddBlocks 1
                      ]
            , sourceCode
            }
    failedCampaign =
        Evaluation
            { wallets =
                  [ mkSimulatorWallet w1 twentyLovelace
                  , mkSimulatorWallet w2 twentyLovelace
                  , mkSimulatorWallet w3 twentyLovelace
                  ]
            , program =
                  toJSONString
                      [ scheduleCollection w1
                      , contribute w2 $ lovelaceValueOf 10
                      , AddBlocks 1
                      , AddBlocksUntil 40
                      , AddBlocksUntil 60
                      , AddBlocksUntil 100
                      ]
            , sourceCode
            }
    scheduleCollection caller = callEndpoint "schedule collection" caller ()
    contribute caller contribValue =
        callEndpoint "contribute" caller $ Contribution {contribValue}

knownCurrencyTest :: TestTree
knownCurrencyTest =
    testCase "should return registered known currencies" $ do
        currencies <- compile source
        hasKnownCurrency currencies
  where
    source =
        SourceCode $
        Text.unlines
            [ "import Playground.Contract"
            , "import Data.Text"
            , "import Data.List.NonEmpty (NonEmpty ((:|)))"
            , "import Ledger.Value (TokenName(TokenName))"
            , "import Ledger.Scripts (ValidatorHash (..))"
            , "import Playground.Types (KnownCurrency (..))"
            , "import Language.PlutusTx.Prelude"
            , ""
            , "myCurrency :: KnownCurrency"
            , "myCurrency = KnownCurrency (ValidatorHash \"\") \"MyCurrency\" (TokenName \"MyToken\" :| [])"
            , "$(mkKnownCurrencies ['myCurrency])"
            , ""
            , "schemas = []"
            , "iotsDefinitions = \"\""
            ]
    expectedCurrencies =
        [ adaCurrency
        , KnownCurrency
              (ValidatorHash "")
              "MyCurrency"
              (TokenName "MyToken" :| [])
        ]
    hasKnownCurrency (Right (InterpreterResult _ (CompilationResult _ currencies))) =
        assertEqual "" expectedCurrencies currencies
    hasKnownCurrency other =
        assertFailure $ "Compilation failed: " <> show other

compile ::
       SourceCode
    -> IO (Either InterpreterError (InterpreterResult CompilationResult))
compile source = runExceptT $ do
  PI.checkCode source
  result <- Webghc.compile maxInterpretationTime False $ over SourceCode PI.mkCompileScript source
  PI.getCompilationResult result

evaluate ::
       Evaluation
    -> IO (Either PlaygroundError (InterpreterResult EvaluationResult))
evaluate evaluation = runExceptT $ do
    expr <- PI.evaluationToExpr evaluation
    result <- mapError InterpreterError $ Webghc.compile maxInterpretationTime False (SourceCode expr)
    PI.decodeEvaluation result

compilationChecks :: SourceCode -> TestTree
compilationChecks source =
    testCase "should compile" $ do
        compiled <- compile source
        case compiled of
            Left err -> assertFailure $ "Compilation failed: " <> show err
            Right _  -> pure ()

-- | Encode a value in JSON, then make a JSON *string* from that
toJSONString :: ToJSON a => a -> JSON.Value
toJSONString = JSON.String . TL.toStrict . JSON.encodeToLazyText

callEndpoint :: ToJSON a => EndpointDescription -> Wallet -> a -> Expression
callEndpoint endpointDescription caller param =
    CallEndpoint
        { caller
        , argumentValues =
              FunctionSchema {endpointDescription, argument = toJSONString param}
        }
