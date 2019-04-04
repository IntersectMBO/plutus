{-# LANGUAGE OverloadedStrings #-}

module Playground.UsecasesSpec
    ( spec
    ) where

import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.Aeson.Types             (object, (.=))
import qualified Data.ByteString.Char8        as BSC
import           Data.Either                  (isRight)
import           Data.List.NonEmpty           (NonEmpty ((:|)))
import           Data.Swagger                 ()
import qualified Data.Text                    as Text
import qualified Data.Text.Lazy               as TL
import           Data.Time.Units              (Microsecond, fromMicroseconds)
import           Language.Haskell.Interpreter (InterpreterError, InterpreterResult (InterpreterResult),
                                               SourceCode (SourceCode))
import           Ledger                       (Blockchain)
import qualified Ledger.Ada                   as Ada
import           Ledger.Validation            (ValidatorHash (ValidatorHash))
import           Playground.API               (CompilationResult (CompilationResult), Evaluation (Evaluation),
                                               Expression (Action, Wait), Fn (Fn), FunctionSchema (FunctionSchema),
                                               KnownCurrency (KnownCurrency), PlaygroundError,
                                               SimpleArgumentSchema (SimpleArraySchema, SimpleIntSchema, SimpleObjectSchema, SimpleStringSchema, SimpleTupleSchema),
                                               SimulatorWallet (SimulatorWallet), TokenId (TokenId), argumentSchema,
                                               functionName, isSupportedByFrontend, simulatorWalletBalance,
                                               simulatorWalletWallet)
import qualified Playground.Interpreter       as PI
import           Playground.Usecases          (crowdfunding, game, messages, vesting)
import           Test.Hspec                   (Spec, describe, it, shouldBe, shouldSatisfy)
import           Wallet.Emulator.Types        (EmulatorEvent, Wallet (Wallet), walletPubKey)

spec :: Spec
spec = do
    vestingSpec
    gameSpec
    messagesSpec
    crowdfundingSpec
    knownCurrencySpec

maxInterpretationTime :: Microsecond
maxInterpretationTime = fromMicroseconds 10000000

vestingSpec :: Spec
vestingSpec =
    describe "vesting" $ do
        compilationChecks vesting
        it "should compile with the expected schema" $ do
            Right (InterpreterResult _ (CompilationResult result _)) <-
                compile vesting
            result `shouldBe`
                [ FunctionSchema
                      { functionName = Fn "vestFunds"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                  , ( "vestingTranche2"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheAmount"
                                            , SimpleObjectSchema
                                                  [("getAda", SimpleIntSchema)])
                                          , ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          ])
                                  , ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheAmount"
                                            , SimpleObjectSchema
                                                  [("getAda", SimpleIntSchema)])
                                          , ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          ])
                                  ]
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "registerVestingScheme"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                  , ( "vestingTranche2"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheAmount"
                                            , SimpleObjectSchema
                                                  [("getAda", SimpleIntSchema)])
                                          , ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          ])
                                  , ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheAmount"
                                            , SimpleObjectSchema
                                                  [("getAda", SimpleIntSchema)])
                                          , ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          ])
                                  ]
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "withdraw"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "vestingOwner"
                                    , SimpleObjectSchema
                                          [("getPubKey", SimpleStringSchema)])
                                    , ( "vestingTranche2"
                                          , SimpleObjectSchema
                                                [ ( "vestingTrancheAmount"
                                                , SimpleObjectSchema
                                                      [("getAda", SimpleIntSchema)])
                                                , ( "vestingTrancheDate"
                                                , SimpleObjectSchema
                                                      [("getSlot", SimpleIntSchema)])
                                          ])
                                  , ( "vestingTranche1"
                                    , SimpleObjectSchema
                                          [ ( "vestingTrancheAmount"
                                            , SimpleObjectSchema
                                                  [("getAda", SimpleIntSchema)])
                                          , ( "vestingTrancheDate"
                                            , SimpleObjectSchema
                                                  [("getSlot", SimpleIntSchema)])
                                          ])
                                  ]
                            , SimpleObjectSchema [("getAda", SimpleIntSchema)]
                            ]
                      }
                , FunctionSchema
                      { functionName = Fn "payToPublicKey_"
                      , argumentSchema =
                            [ SimpleObjectSchema
                                  [ ( "ivTo"
                                    , SimpleObjectSchema
                                          [("getSlot", SimpleIntSchema)])
                                  , ( "ivFrom"
                                    , SimpleObjectSchema
                                          [("getSlot", SimpleIntSchema)])
                                  ]
                            , SimpleObjectSchema
                                  [ ( "getValue"
                                    , SimpleObjectSchema
                                        [("unMap", SimpleArraySchema (SimpleTupleSchema (SimpleIntSchema, SimpleIntSchema)))])
                                  ]
                            , SimpleObjectSchema
                                  [("getPubKey", SimpleStringSchema)]
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
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            ]
            []
            (sourceCode vesting)
            []
    simpleWaitEval =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            ]
            [Wait 10]
            (sourceCode vesting)
            []
    vestFundsEval =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action
                  (Fn "vestFunds")
                  (Wallet 1)
                  [ theVesting ]
            ]
            (sourceCode vesting)
            []
    theVesting = toJSONString $
          object
                  [ "vestingTranche1" .= object
                        [ "vestingTrancheDate" .= object [ "getSlot" .= mkI 1]
                        , "vestingTrancheAmount" .= object [ "getAda" .= mkI 1]
                        ]
                  , "vestingTranche2" .= object
                        [ "vestingTrancheDate" .= object ["getSlot" .= mkI 1]
                        , "vestingTrancheAmount" .= object [ "getAda" .= mkI 1]
                        ]
                  , "vestingOwner" .= JSON.toJSON (walletPubKey (Wallet 1))
                  ]

gameSpec :: Spec
gameSpec =
    describe "game" $ do
        compilationChecks game
        it "should unlock the funds" $
            evaluate gameEvalSuccess >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ SimulatorWallet
                                       { simulatorWalletWallet = Wallet 1
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 12
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 2
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 8
                                       }
                                 ])
        it "should keep the funds" $
            evaluate gameEvalFailure >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ SimulatorWallet
                                       { simulatorWalletWallet = Wallet 1
                                       , simulatorWalletBalance = ten
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 2
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 8
                                       }
                                 ])
        it
            "Sequential fund transfer fails - 'Game' script - 'payToPublicKey_' action" $
            evaluate payAll >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ SimulatorWallet
                                       { simulatorWalletWallet = Wallet 1
                                       , simulatorWalletBalance = ten
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 2
                                       , simulatorWalletBalance = ten
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 3
                                       , simulatorWalletBalance = ten
                                       }
                                 ])
  where
    ten = Ada.adaValueOf 10
    gameEvalFailure =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 2
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action (Fn "startGame") (Wallet 1) []
            , Action
                  (Fn "lock")
                  (Wallet 2)
                  [JSON.String "\"abcde\"", JSON.String "{\"getAda\": 2}"]
            , Action (Fn "guess") (Wallet 1) [JSON.String "\"ade\""]
            ]
            (sourceCode game)
            []
    gameEvalSuccess =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 2
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action (Fn "startGame") (Wallet 1) []
            , Action
                  (Fn "lock")
                  (Wallet 2)
                  [JSON.String "\"abcde\"", JSON.String "{\"getAda\": 2}"]
            , Action (Fn "guess") (Wallet 1) [JSON.String "\"abcde\""]
            ]
            (sourceCode game)
            []
    payAll =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 2
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 3
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action
                  (Fn "payToPublicKey_")
                  (Wallet 1)
                  [ slotRange
                  , nineAda
                  , toJSONString (walletPubKey (Wallet 2))
                  ]
            , Action
                  (Fn "payToPublicKey_")
                  (Wallet 2)
                  [ slotRange
                  , nineAda
                  , toJSONString (walletPubKey (Wallet 3))
                  ]
            , Action
                  (Fn "payToPublicKey_")
                  (Wallet 3)
                  [ slotRange
                  , nineAda
                  , toJSONString (walletPubKey (Wallet 1))
                  ]
            ]
            (sourceCode game)
            []
    slotRange = JSON.String "{\"ivTo\":null,\"ivFrom\":null}"
    nineAda = toJSONString $ Ada.adaValueOf 9

hasFundsDistribution ::
       [SimulatorWallet]
    -> Either PlaygroundError (InterpreterResult ( Blockchain
                                                 , [EmulatorEvent]
                                                 , [SimulatorWallet]))
    -> Bool
hasFundsDistribution _ (Left _) = False
hasFundsDistribution requiredDistribution (Right (InterpreterResult _ (_, _, actualDistribution))) =
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
                                 [ SimulatorWallet
                                       { simulatorWalletWallet = Wallet 1
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 26
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 2
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 2
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 3
                                       , simulatorWalletBalance =
                                             Ada.adaValueOf 2
                                       }
                                 ])
        it "should run failed campaign" $
            evaluate failedCampaign >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ SimulatorWallet
                                       { simulatorWalletWallet = Wallet 1
                                       , simulatorWalletBalance = ten
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 2
                                       , simulatorWalletBalance = ten
                                       }
                                 , SimulatorWallet
                                       { simulatorWalletWallet = Wallet 3
                                       , simulatorWalletBalance = ten
                                       }
                                 ])
  where
    ten = Ada.adaValueOf 10
    failedCampaign =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 2
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 3
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action (Fn "scheduleCollection") (Wallet 1) [theCampaign]
            , Action (Fn "contribute") (Wallet 2) [theCampaign, theContribution]
            , Wait 20
            ]
            (sourceCode crowdfunding)
            []
    successfulCampaign =
        Evaluation
            [ SimulatorWallet
                  { simulatorWalletWallet = Wallet 1
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 2
                  , simulatorWalletBalance = ten
                  }
            , SimulatorWallet
                  { simulatorWalletWallet = Wallet 3
                  , simulatorWalletBalance = ten
                  }
            ]
            [ Action (Fn "scheduleCollection") (Wallet 1) [theCampaign]
            , Action (Fn "contribute") (Wallet 2) [theCampaign, theContribution]
            , Action (Fn "contribute") (Wallet 3) [theCampaign, theContribution]
            , Wait 10
            ]
            (sourceCode crowdfunding)
            []

    theCampaign = toJSONString $
        object
            [ "campaignDeadline" .= object ["getSlot" .= mkI 10]
            , "campaignTarget" .= object ["getAda" .= mkI 15]
            , "campaignCollectionDeadline" .= object ["getSlot" .= mkI 20]
            , "campaignOwner" .= walletPubKey (Wallet 1)
            ]
    theContribution = toJSONString $ object ["getAda" .= mkI 8]

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
            , "import Ledger.Validation (ValidatorHash (..))"
            , "import Playground.API (KnownCurrency (..), TokenId (..))"
            , "myCurrency :: KnownCurrency"
            , "myCurrency = KnownCurrency (ValidatorHash \"\") \"MyCurrency\" (TokenId \"MyToken\" :| [])"
            , "$(mkKnownCurrencies ['myCurrency])"
            ]
    hasKnownCurrency (Right (InterpreterResult _ (CompilationResult _ [KnownCurrency (ValidatorHash "") "MyCurrency" (TokenId "MyToken" :| [])]))) =
        True
    hasKnownCurrency _ = False

sourceCode :: BSC.ByteString -> SourceCode
sourceCode = SourceCode . Text.pack . BSC.unpack

compile ::
       BSC.ByteString
    -> IO (Either InterpreterError (InterpreterResult CompilationResult))
compile = runExceptT . PI.compile maxInterpretationTime . sourceCode

evaluate ::
       Evaluation
    -> IO (Either PlaygroundError (InterpreterResult ( Blockchain
                                                     , [EmulatorEvent]
                                                     , [SimulatorWallet])))
evaluate evaluation =
    runExceptT $ PI.runFunction maxInterpretationTime evaluation

compilationChecks :: BSC.ByteString -> Spec
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
