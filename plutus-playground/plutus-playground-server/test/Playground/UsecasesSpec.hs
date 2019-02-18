{-# LANGUAGE OverloadedStrings #-}

module Playground.UsecasesSpec
    ( spec
    ) where

import           Control.Monad.Except   (runExceptT)
import qualified Data.Aeson             as JSON
import qualified Data.Aeson.Text        as JSON
import           Data.Aeson.Types       (object, (.=))
import qualified Data.ByteString.Char8  as BSC
import           Data.Either            (isRight)
import qualified Data.Text              as Text
import qualified Data.Text.Lazy         as TL
import qualified Ledger.Ada             as Ada
import           Ledger.Types           (Blockchain)
import           Playground.API         (Evaluation (Evaluation), Expression (Action, Wait), Fn (Fn), FunctionSchema,
                                         PlaygroundError, SimpleArgumentSchema, SourceCode (SourceCode), functionSchema)
import qualified Playground.Interpreter as PI
import           Playground.Usecases    (crowdfunding, game, messages, vesting)
import           Test.Hspec             (Spec, describe, it, shouldSatisfy)
import           Wallet.Emulator.Types  (EmulatorEvent, Wallet (Wallet))

spec :: Spec
spec = do
    vestingSpec
    gameSpec
    messagesSpec
    crowdfundingSpec

vestingSpec :: Spec
vestingSpec =
    describe "vesting" $ do
        it "should compile" $ compile vesting >>= (`shouldSatisfy` isRight)
        it "should run simple evaluation" $
            evaluate simpleEvaluation >>= (`shouldSatisfy` isRight)
        it "should run simple wait evaluation" $
            evaluate simpleWaitEval >>= (`shouldSatisfy` isRight)
        it "should run vest funds evaluation" $
            evaluate vestFundsEval >>= (`shouldSatisfy` isRight)
  where
    simpleEvaluation = Evaluation [(Wallet 1, 10)] [] (sourceCode vesting) []
    simpleWaitEval =
        Evaluation [(Wallet 1, 10)] [Wait 10] (sourceCode vesting) []
    vestFundsEval =
        Evaluation
            [(Wallet 1, 10)]
            [ Action
                  (Fn "vestFunds")
                  (Wallet 1)
                  [ JSON.String
                        "{\"vestingTranche1\":{\"vestingTrancheDate\":{\"getSlot\":1},\"vestingTrancheAmount\":{\"getAda\":1}},\"vestingTranche2\":{\"vestingTrancheDate\":{\"getSlot\":1},\"vestingTrancheAmount\":{\"getAda\":1}},\"vestingOwner\":{\"getPubKey\":1}}"
                  , JSON.String "{\"getAda\": 1}"
                  ]
            ]
            (sourceCode vesting)
            []

gameSpec :: Spec
gameSpec =
    describe "game" $ do
        it "should compile" $ compile game >>= (`shouldSatisfy` isRight)
        it "should unlock the funds" $
            evaluate gameEvalSuccess >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [(Wallet 1, Ada.fromInt  12), (Wallet 2, Ada.fromInt  8)])
        it "should keep the funds" $
            evaluate gameEvalFailure >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [(Wallet 1, ten), (Wallet 2, Ada.fromInt  8)])
        it
            "Sequential fund transfer fails - 'Game' script - 'payToPublicKey_' action" $
            evaluate payAll >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ (Wallet 1, ten)
                                 , (Wallet 2, ten)
                                 , (Wallet 3, ten)
                                 ])
  where
    ten = Ada.fromInt 10
    gameEvalFailure =
        Evaluation
            [(Wallet 1, 10), (Wallet 2, 10)]
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
            [(Wallet 1, 10), (Wallet 2, 10)]
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
            [(Wallet 1, 10), (Wallet 2, 10), (Wallet 3, 10)]
            [ Action
                  (Fn "payToPublicKey_")
                  (Wallet 1)
                  [ slotRange
                  , JSON.String "{\"getValue\":[[0,9]]}"
                  , JSON.String "{\"getPubKey\":2}"
                  ]
            , Action
                  (Fn "payToPublicKey_")
                  (Wallet 2)
                  [ slotRange
                  , JSON.String "{\"getValue\":[[0,9]]}"
                  , JSON.String "{\"getPubKey\":3}"
                  ]
            , Action
                  (Fn "payToPublicKey_")
                  (Wallet 3)
                  [ slotRange
                  , JSON.String "{\"getValue\":[[0,9]]}"
                  , JSON.String "{\"getPubKey\":1}"
                  ]
            ]
            (sourceCode game)
            []
    slotRange = JSON.String "{\"ivTo\":null,\"ivFrom\":null}"

hasFundsDistribution ::
       [(Wallet, Ada.Ada)]
    -> Either PlaygroundError (Blockchain, [EmulatorEvent], [(Wallet, Ada.Ada)])
    -> Bool
hasFundsDistribution _ (Left _) = False
hasFundsDistribution requiredDistribution (Right (_, _, actualDistribution)) =
    requiredDistribution == actualDistribution

messagesSpec :: Spec
messagesSpec =
    describe "messages" $
    it "should compile" $ compile messages >>= (`shouldSatisfy` isRight)

crowdfundingSpec :: Spec
crowdfundingSpec =
    describe "crowdfunding" $ do
        it "should compile" $ compile crowdfunding >>= (`shouldSatisfy` isRight)
        it "should run successful campaign" $
            evaluate successfulCampaign >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [(Wallet 1, Ada.fromInt  26), (Wallet 2, Ada.fromInt  2), (Wallet 3, Ada.fromInt  2)])
        it "should run failed campaign" $
            evaluate failedCampaign >>=
            (`shouldSatisfy` hasFundsDistribution
                                 [ (Wallet 1, ten)
                                 , (Wallet 2, ten)
                                 , (Wallet 3, ten)
                                 ])
  where
    ten = Ada.fromInt  10
    failedCampaign =
        Evaluation
            [(Wallet 1, 10), (Wallet 2, 10), (Wallet 3, 10)]
            [ Action (Fn "scheduleCollection") (Wallet 1) [theCampaign]
            , Action (Fn "contribute") (Wallet 2) [theCampaign, theContribution]
            , Wait 20
            ]
            (sourceCode crowdfunding)
            []
    successfulCampaign =
        Evaluation
            [(Wallet 1, 10), (Wallet 2, 10), (Wallet 3, 10)]
            [ Action (Fn "scheduleCollection") (Wallet 1) [theCampaign]
            , Action (Fn "contribute") (Wallet 2) [theCampaign, theContribution]
            , Action (Fn "contribute") (Wallet 3) [theCampaign, theContribution]
            , Wait 10
            ]
            (sourceCode crowdfunding)
            []
    mkI :: Int -> JSON.Value
    mkI = JSON.toJSON
    theCampaign =
        JSON.String $
        TL.toStrict $
        JSON.encodeToLazyText $
        object
            [ "campaignDeadline" .= object ["getSlot" .= mkI 10]
            , "campaignTarget" .= object ["getAda" .= mkI 15]
            , "campaignCollectionDeadline" .= object ["getSlot" .= mkI 20]
            , "campaignOwner" .= object ["getPubKey" .= mkI 1]
            ]
    theContribution =
        JSON.String $
        TL.toStrict $ JSON.encodeToLazyText $ object ["getAda" .= mkI 8]

sourceCode :: BSC.ByteString -> SourceCode
sourceCode = SourceCode . Text.pack . BSC.unpack

compile ::
       BSC.ByteString
    -> IO (Either PlaygroundError [FunctionSchema SimpleArgumentSchema])
compile = runExceptT . fmap functionSchema . PI.compile . sourceCode

evaluate ::
       Evaluation
    -> IO (Either PlaygroundError ( Blockchain
                                  , [EmulatorEvent]
                                  , [(Wallet, Ada.Ada)]))
evaluate evaluation = runExceptT $ PI.runFunction evaluation
