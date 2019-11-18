{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Playground.UsecasesSpec
    ( tests
    ) where

import           Control.Monad                (unless)
import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.Foldable                (traverse_)
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.IO                 as Text
import qualified Data.Text.Lazy               as TL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult (InterpreterResult, result),
                                               SourceCode (SourceCode))
import qualified Ledger.Ada                   as Ada
import           Ledger.Scripts               (ValidatorHash (ValidatorHash))
import           Ledger.Value                 (TokenName (TokenName), Value)
import qualified Playground.Interpreter       as PI
import           Playground.Types             (CompilationResult (CompilationResult), EndpointName (EndpointName),
                                               Evaluation (Evaluation, program, sourceCode, wallets),
                                               EvaluationResult (EvaluationResult, emulatorLog, fundsDistribution, resultBlockchain, walletKeys),
                                               Expression (AddBlocks, CallEndpoint, PayToWallet, arguments, destination, endpointName, source, value, wallet),
                                               FunctionSchema (FunctionSchema), KnownCurrency (KnownCurrency),
                                               PlaygroundError, SimulatorWallet (SimulatorWallet), adaCurrency,
                                               argumentSchema, functionName, simulatorWalletBalance,
                                               simulatorWalletWallet)
import           Playground.Usecases          (crowdfunding, errorHandling, game, vesting)
import           Schema                       (FormSchema (FormSchemaInt, FormSchemaObject, FormSchemaUnit, FormSchemaValue))
import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.HUnit             (Assertion, assertEqual, assertFailure, testCase)
import           Wallet.Emulator.Types        (Wallet (Wallet), walletPubKey)
import           Wallet.Rollup.Render         (showBlockchain)

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

maxInterpretationTime :: Microsecond
maxInterpretationTime = fromMicroseconds 100000000

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
              Right (InterpreterResult _ (CompilationResult result _ _)) <-
                  compile vesting
              assertEqual
                  ""
                  result
                  [ FunctionSchema
                        { functionName = EndpointName "retrieve funds"
                        , argumentSchema = [FormSchemaValue]
                        }
                  , FunctionSchema
                        { functionName = EndpointName "vest funds"
                        , argumentSchema = [FormSchemaUnit]
                        }
                  , FunctionSchema
                        { functionName = EndpointName "payToWallet_"
                        , argumentSchema =
                              [ FormSchemaValue
                              , FormSchemaObject [("getWallet", FormSchemaInt)]
                              ]
                        }
                  ]
        , testCase "should run simple evaluation" $
          evaluate simpleEvaluation >>=
          hasFundsDistribution
              [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 tenAda]
        , testCase "should run simple wait evaluation" $
          evaluate simpleAddBlocksEval >>=
          hasFundsDistribution
              [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 tenAda]
        , testCase "should run vest funds evaluation" $
          evaluate vestFundsEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ Ada.adaValueOf 10
              , mkSimulatorWallet w2 $ Ada.adaValueOf 2
              ]
        , testCase "should run vest and a partial retrieve of funds" $
          evaluate vestAndPartialRetrieveEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ Ada.adaValueOf 15
              , mkSimulatorWallet w2 $ Ada.adaValueOf 2
              ]
        , testCase "should run vest and a partial retrieve of funds" $
          evaluate vestAndFullRetrieveEval >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 $ Ada.adaValueOf 18
              , mkSimulatorWallet w2 $ Ada.adaValueOf 2
              ]
        ]
  where
    tenAda = Ada.adaValueOf 10
    wallets = [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 tenAda]
    sourceCode = SourceCode vesting
    simpleEvaluation =
        Evaluation
            {wallets, sourceCode, program = toJSONString ([] :: [Expression s])}
    simpleAddBlocksEval =
        Evaluation {wallets, sourceCode, program = toJSONString [AddBlocks 10]}
    vestFundsEval =
        Evaluation
            { wallets
            , sourceCode
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "vest funds"
                            , wallet = w2
                            , arguments = toEndpointParam ()
                            }
                      ]
            }
    vestAndPartialRetrieveEval =
        Evaluation
            { wallets
            , sourceCode
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "vest funds"
                            , wallet = w2
                            , arguments = toEndpointParam ()
                            }
                      , AddBlocks 10
                      , CallEndpoint
                            { endpointName = EndpointName "retrieve funds"
                            , wallet = w1
                            , arguments = toEndpointParam $ Ada.adaValueOf 5
                            }
                      , AddBlocks 5
                      ]
            }
    vestAndFullRetrieveEval =
        Evaluation
            { wallets
            , sourceCode
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "vest funds"
                            , wallet = w2
                            , arguments = toEndpointParam ()
                            }
                      , AddBlocks 40
                      , CallEndpoint
                            { endpointName = EndpointName "retrieve funds"
                            , wallet = w1
                            , arguments = toEndpointParam $ Ada.adaValueOf 8
                            }
                      , AddBlocks 5
                      ]
            }

gameTest :: TestTree
gameTest =
    testGroup
        "game"
        [ compilationChecks game
        , testCase "should keep the funds" $
          evaluate gameEvalFailure >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 tenAda
              , mkSimulatorWallet w2 (Ada.adaValueOf 8)
              ]
        , testCase "should unlock the funds" $
          evaluate gameEvalSuccess >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 (Ada.adaValueOf 12)
              , mkSimulatorWallet w2 (Ada.adaValueOf 8)
              ]
        , testCase
              "Sequential fund transfer - deleting wallets 'payToWallet_' action" $
          evaluate (payAll w3 w4 w5) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w3 tenAda
              , mkSimulatorWallet w4 tenAda
              , mkSimulatorWallet w5 tenAda
              ]
        , testCase "Sequential fund transfer - 'payToWallet_' action" $
          evaluate (payAll w1 w2 w3) >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 tenAda
              , mkSimulatorWallet w2 tenAda
              , mkSimulatorWallet w3 tenAda
              ]
        ]
  where
    tenAda = Ada.adaValueOf 10
    sourceCode = SourceCode game
    wallets = [mkSimulatorWallet w1 tenAda, mkSimulatorWallet w2 tenAda]
    gameEvalFailure =
        Evaluation
            { sourceCode
            , wallets
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "lock"
                            , wallet = w2
                            , arguments =
                                  toEndpointParam $
                                  JSON.object
                                      [ ("secretWord", "abcde")
                                      , ("amount", JSON.toJSON twoAda)
                                      ]
                            }
                      , CallEndpoint
                            { endpointName = EndpointName "guess"
                            , wallet = w1
                            , arguments =
                                  toEndpointParam $
                                  JSON.object [("guessWord", "ade")]
                            }
                      ]
            }
    gameEvalSuccess =
        Evaluation
            { sourceCode
            , wallets
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "lock"
                            , wallet = w2
                            , arguments =
                                  toEndpointParam $
                                  JSON.object
                                      [ ("secretWord", "abcde")
                                      , ("amount", JSON.toJSON twoAda)
                                      ]
                            }
                      , CallEndpoint
                            { endpointName = EndpointName "guess"
                            , wallet = w1
                            , arguments =
                                  toEndpointParam $
                                  JSON.object [("guessWord", "abcde")]
                            }
                      ]
            }
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
                      [ PayToWallet
                            {source = a, destination = b, value = nineAda}
                      , PayToWallet
                            {source = b, destination = c, value = nineAda}
                      , PayToWallet
                            {source = c, destination = a, value = nineAda}
                      ]
            }
    nineAda = Ada.adaValueOf 9
    twoAda = Ada.adaOf 2

hasFundsDistribution ::
       [SimulatorWallet]
    -> Either PlaygroundError (InterpreterResult EvaluationResult)
    -> Assertion
hasFundsDistribution _ (Left err) = assertFailure $ show err
hasFundsDistribution requiredDistribution (Right InterpreterResult {result = EvaluationResult {..}}) = do
    unless (requiredDistribution == fundsDistribution) $ do
        Text.putStrLn $
            either id id $ showBlockchain walletKeys resultBlockchain
        traverse_ print $ reverse emulatorLog
    assertEqual "" requiredDistribution fundsDistribution

errorHandlingTest :: TestTree
errorHandlingTest = testGroup "errorHandling" [compilationChecks errorHandling]

crowdfundingTest :: TestTree
crowdfundingTest =
    testGroup
        "crowdfunding"
        [ compilationChecks crowdfunding
        , testCase "should run successful campaign" $
          evaluate successfulCampaign >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 (Ada.lovelaceValueOf 20000020)
              , mkSimulatorWallet w2 (Ada.lovelaceValueOf 19999990)
              , mkSimulatorWallet w3 (Ada.lovelaceValueOf 19999990)
              ]
        , testCase "should run failed campaign and return the funds" $
          evaluate failedCampaign >>=
          hasFundsDistribution
              [ mkSimulatorWallet w1 twentyAda
              , mkSimulatorWallet w2 twentyAda
              , mkSimulatorWallet w3 twentyAda
              ]
        ]
  where
    twentyAda = Ada.adaValueOf 20
    successfulCampaign =
        Evaluation
            { wallets =
                  [ mkSimulatorWallet w1 twentyAda
                  , mkSimulatorWallet w2 twentyAda
                  , mkSimulatorWallet w3 twentyAda
                  ]
            , program =
                  toJSONString
                      [ AddBlocks 1
                      , CallEndpoint
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
                                        , JSON.toJSON $ Ada.lovelaceValueOf 10)
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
                                        , JSON.toJSON $ Ada.lovelaceValueOf 10)
                                      ]
                            }
                      , AddBlocks 10
                      ]
            , sourceCode = SourceCode crowdfunding
            }
    failedCampaign =
        Evaluation
            { wallets =
                  [ mkSimulatorWallet w1 twentyAda
                  , mkSimulatorWallet w2 twentyAda
                  , mkSimulatorWallet w3 twentyAda
                  ]
            , program =
                  toJSONString
                      [ CallEndpoint
                            { endpointName = EndpointName "schedule collection"
                            , wallet = w1
                            , arguments = toEndpointParam ()
                            }
                      , AddBlocks 1
                      , CallEndpoint
                            { endpointName = EndpointName "contribute"
                            , wallet = w2
                            , arguments =
                                  toEndpointParam $
                                  JSON.object
                                      [ ( "contributor"
                                        , JSON.toJSON $ walletPubKey w2)
                                      , ( "contribValue"
                                        , JSON.toJSON $ Ada.lovelaceValueOf 10)
                                      ]
                            }
                      , AddBlocks 10
                      , AddBlocks 40
                      ]
            , sourceCode = SourceCode crowdfunding
            }

knownCurrencyTest :: TestTree
knownCurrencyTest =
    testCase "should return registered known currencies" $ do
        currencies <- runExceptT $ PI.compile maxInterpretationTime code
        hasKnownCurrency currencies
  where
    code =
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
    hasKnownCurrency (Right (InterpreterResult _ (CompilationResult _ currencies _))) =
        assertEqual "" expectedCurrencies currencies
    hasKnownCurrency other =
        assertFailure $ "Compilation failed: " <> show other

compile ::
       Text
    -> IO (Either InterpreterError (InterpreterResult CompilationResult))
compile = runExceptT . PI.compile maxInterpretationTime . SourceCode

evaluate ::
       Evaluation
    -> IO (Either PlaygroundError (InterpreterResult EvaluationResult))
evaluate evaluation =
    runExceptT $ PI.runFunction maxInterpretationTime evaluation

compilationChecks :: Text -> TestTree
compilationChecks source =
    testCase "should compile" $ do
        compiled <- compile source
        case compiled of
            Left err -> assertFailure $ "Compilation failed: " <> show err
            Right _  -> pure ()

-- | Encode a value in JSON, then make a JSON *string* from that
toJSONString :: JSON.ToJSON a => a -> JSON.Value
toJSONString = JSON.String . TL.toStrict . JSON.encodeToLazyText

toEndpointParam :: JSON.ToJSON a => a -> JSON.Value
toEndpointParam arg = toJSONString [arg]
