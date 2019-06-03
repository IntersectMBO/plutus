{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

module Playground.UsecasesSpec
    ( spec
    ) where

import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.Aeson.Types             (object, (.=))
import           Data.Either                  (isRight)
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import qualified Data.Text                    as Text
import qualified Data.Text.Lazy               as TL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult (InterpreterResult),
                                               SourceCode (SourceCode))
import qualified Ledger.Ada                   as Ada
import           Ledger.Validation            (ValidatorHash (ValidatorHash))
import           Ledger.Value                 (TokenName (TokenName), Value)
import           Playground.API               (CompilationResult (CompilationResult), Evaluation (Evaluation),
                                               Expression (Action, Wait), Fn (Fn), FunctionSchema (FunctionSchema),
                                               KnownCurrency (KnownCurrency), PlaygroundError,
                                               SimulatorWallet (SimulatorWallet), adaCurrency, argumentSchema,
                                               functionName, isSupportedByFrontend, simulatorWalletBalance,
                                               simulatorWalletWallet)
import qualified Playground.Interpreter       as PI
import           Playground.Interpreter.Util  (TraceResult)
import           Playground.Usecases          (crowdfunding, game, messages, vesting)
import           Schema                       ()
import           Schema                       (SimpleArgumentSchema (SimpleArraySchema, SimpleHexSchema, SimpleIntSchema, SimpleObjectSchema, SimpleStringSchema, SimpleTupleSchema, ValueSchema))
import           Test.Hspec                   (Spec, describe, it, shouldBe, shouldSatisfy)
import           Wallet.Emulator.Types        (Wallet (Wallet), walletPubKey)

spec :: Spec
spec = do
    vestingSpec
    gameSpec
    messagesSpec
    crowdfundingSpec
    knownCurrencySpec

maxInterpretationTime :: Microsecond
maxInterpretationTime = fromMicroseconds 40000000

w1, w2, w3, w4, w5 :: Wallet
w1 = Wallet 1

w2 = Wallet 2

w3 = Wallet 3

w4 = Wallet 4

w5 = Wallet 5

mkSimulatorWallet :: Wallet -> Value -> SimulatorWallet
mkSimulatorWallet simulatorWalletWallet simulatorWalletBalance =
    SimulatorWallet {..}

vestingSpec :: Spec
vestingSpec =
    describe "vesting" $ do
        let vlSchema =
                ValueSchema
                    [ ( "getValue"
                      , SimpleArraySchema
                            (SimpleTupleSchema
                                 ( SimpleHexSchema
                                 , SimpleArraySchema
                                       (SimpleTupleSchema
                                            ( SimpleStringSchema
                                            , SimpleIntSchema)))))
                    ]
        compilationChecks vesting
        it "should compile with the expected schema" $ do
            Right (InterpreterResult _ (CompilationResult result _)) <-
                compile vesting
            result `shouldBe`
                [ FunctionSchema
                      { functionName = Fn "vestFunds"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingTranche2"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                  ]
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "registerVestingScheme"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingTranche2"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                  ]
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "withdraw"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingTranche2"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          , ("vestingTrancheAmount", vlSchema)
                                          ])
                                  , ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                  ]
                            , vlSchema
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "payToWallet_"
                      , argumentSchema =
                            [ vlSchema
                            , SimpleObjectSchema
                                  [("getWallet", SimpleIntSchema)]
                            ]
                      }
                ]
        it "should run simple evaluation" $
            evaluate simpleEvaluation >>= (`shouldSatisfy` isRight)
        it "should run simple wait evaluation" $
            evaluate simpleWaitEval >>= (`shouldSatisfy` isRight)
        it "should run vest funds evaluation" $
            evaluate vestFundsEval >>= (`shouldSatisfy` isRight)
  where
    ten = Ada.adaValueOf 10
    simpleEvaluation =
        Evaluation [mkSimulatorWallet w1 ten] [] (SourceCode vesting) []
    simpleWaitEval =
        Evaluation [mkSimulatorWallet w1 ten] [Wait 10] (SourceCode vesting) []
    vestFundsEval =
        Evaluation
            [mkSimulatorWallet w1 ten]
            [Action (Fn "vestFunds") w1 [theVesting]]
            (SourceCode vesting)
            []
    theVesting =
        toJSONString $
        object
            [ "vestingTranche1" .=
              object
                  [ "vestingTrancheDate" .= object ["getSlot" .= mkI 1]
                  , "vestingTrancheAmount" .= JSON.toJSON (Ada.adaValueOf 1)
                  ]
            , "vestingTranche2" .=
              object
                  [ "vestingTrancheDate" .= object ["getSlot" .= mkI 1]
                  , "vestingTrancheAmount" .= JSON.toJSON (Ada.adaValueOf 1)
                  ]
            , "vestingOwner" .= JSON.toJSON (walletPubKey w1)
            ]

gameSpec :: Spec
gameSpec =
    describe "game" $ do
        compilationChecks game
        it "should unlock the funds" $
            evaluate gameEvalSuccess >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w1 (Ada.adaValueOf 12)
                                 , mkSimulatorWallet w2 (Ada.adaValueOf 8)
                                 ])
        it "should keep the funds" $
            evaluate gameEvalFailure >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w1 ten
                                 , mkSimulatorWallet w2 (Ada.adaValueOf 8)
                                 ])
        it "Sequential fund transfer - deleting wallets 'payToWallet_' action" $
            evaluate (payAll w3 w4 w5) >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w3 ten
                                 , mkSimulatorWallet w4 ten
                                 , mkSimulatorWallet w5 ten
                                 ])
        it "Sequential fund transfer - 'payToWallet_' action" $
            evaluate (payAll w1 w2 w3) >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w1 ten
                                 , mkSimulatorWallet w2 ten
                                 , mkSimulatorWallet w3 ten
                                 ])
  where
    ten = Ada.adaValueOf 10
    gameEvalFailure =
        Evaluation
            [mkSimulatorWallet w1 ten, mkSimulatorWallet w2 ten]
            [ Action (Fn "startGame") w1 []
            , Action (Fn "lock") w2 [JSON.String "\"abcde\"", twoAda]
            , Action (Fn "guess") w1 [JSON.String "\"ade\""]
            ]
            (SourceCode game)
            []
    gameEvalSuccess =
        Evaluation
            [mkSimulatorWallet w1 ten, mkSimulatorWallet w2 ten]
            [ Action (Fn "startGame") w1 []
            , Action (Fn "lock") w2 [JSON.String "\"abcde\"", twoAda]
            , Action (Fn "guess") w1 [JSON.String "\"abcde\""]
            ]
            (SourceCode game)
            []
    payAll a b c =
        Evaluation
            [ mkSimulatorWallet a ten
            , mkSimulatorWallet b ten
            , mkSimulatorWallet c ten
            ]
            [ Action (Fn "payToWallet_") a [nineAda, toJSONString b]
            , Action (Fn "payToWallet_") b [nineAda, toJSONString c]
            , Action (Fn "payToWallet_") c [nineAda, toJSONString a]
            ]
            (SourceCode game)
            []
    nineAda = toJSONString $ Ada.adaValueOf 9
    twoAda = toJSONString $ Ada.adaValueOf 2

hasFundsDistribution ::
       [SimulatorWallet]
    -> Either PlaygroundError (InterpreterResult TraceResult)
    -> Bool
hasFundsDistribution _ (Left _) = False
hasFundsDistribution requiredDistribution (Right (InterpreterResult _ (_, _, actualDistribution, _))) =
    requiredDistribution == actualDistribution

messagesSpec :: Spec
messagesSpec = describe "messages" $ compilationChecks messages

crowdfundingSpec :: Spec
crowdfundingSpec =
    describe "crowdfunding" $ do
        compilationChecks crowdfunding
        it "should run successful campaign" $
            evaluate successfulCampaign >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w1 (Ada.adaValueOf 26)
                                 , mkSimulatorWallet w2 (Ada.adaValueOf 2)
                                 , mkSimulatorWallet w3 (Ada.adaValueOf 2)
                                 ])
        it "should run failed campaign" $
            evaluate failedCampaign >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ mkSimulatorWallet w1 ten
                                 , mkSimulatorWallet w2 ten
                                 , mkSimulatorWallet w3 ten
                                 ])
  where
    ten = Ada.adaValueOf 10
    failedCampaign =
        Evaluation
            [ mkSimulatorWallet w1 ten
            , mkSimulatorWallet w2 ten
            , mkSimulatorWallet w3 ten
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
            , Wait 20
            ]
            (SourceCode crowdfunding)
            []
    successfulCampaign =
        Evaluation
            [ mkSimulatorWallet w1 ten
            , mkSimulatorWallet w2 ten
            , mkSimulatorWallet w3 ten
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
    theDeadline = toJSONString (object ["getSlot" .= mkI 10])
    theTarget = toJSONString (Ada.adaValueOf 10)
    theCollectionDeadline = toJSONString (object ["getSlot" .= mkI 20])
    theWallet = toJSONString w1
    theContribution = toJSONString $ Ada.adaValueOf 8

knownCurrencySpec :: Spec
knownCurrencySpec =
    describe "mkKnownCurrencies" $
    it "should return registered known currencies" $
    (runExceptT . PI.compile maxInterpretationTime) code >>=
    (`shouldSatisfy` hasKnownCurrency)
  where
    code =
        SourceCode $
        Text.unlines
            [ "import Playground.Contract"
            , "import Data.List.NonEmpty (NonEmpty ((:|)))"
            , "import Ledger.Value (TokenName(TokenName))"
            , "import Ledger.Validation (ValidatorHash (..))"
            , "import Playground.API (KnownCurrency (..))"
            , "import Language.PlutusTx.Prelude"
            , "myCurrency :: KnownCurrency"
            , "myCurrency = KnownCurrency (ValidatorHash \"\") \"MyCurrency\" (TokenName \"MyToken\" :| [])"
            , "$(mkKnownCurrencies ['myCurrency])"
            ]
    hasKnownCurrency (Right (InterpreterResult _ (CompilationResult _ [cur1, cur2]))) =
        cur1 == adaCurrency &&
        cur2 ==
        KnownCurrency
            (ValidatorHash "")
            "MyCurrency"
            (TokenName "MyToken" :| [])
    hasKnownCurrency _ = False

compile ::
       Text.Text
    -> IO (Either InterpreterError (InterpreterResult CompilationResult))
compile = runExceptT . PI.compile maxInterpretationTime . SourceCode

evaluate ::
       Evaluation -> IO (Either PlaygroundError (InterpreterResult TraceResult))
evaluate evaluation =
    runExceptT $ PI.runFunction maxInterpretationTime evaluation

compilationChecks :: Text.Text -> Spec
compilationChecks f = do
    it "should compile" $ compile f >>= (`shouldSatisfy` isRight)
    it "should be representable on the frontend" $
        compile f >>= (`shouldSatisfy` isSupportedCompilationResult)

isSupportedCompilationResult ::
       Either InterpreterError (InterpreterResult CompilationResult) -> Bool
isSupportedCompilationResult (Left _) = False
isSupportedCompilationResult (Right (InterpreterResult _ (CompilationResult functionSchemas _))) =
    all (all isSupportedByFrontend . argumentSchema) functionSchemas

mkI :: Int -> JSON.Value
mkI = JSON.toJSON

-- | Encode a value in JSON, then make a JSON *string* from that
toJSONString :: JSON.ToJSON a => a -> JSON.Value
toJSONString = JSON.String . TL.toStrict . JSON.encodeToLazyText
