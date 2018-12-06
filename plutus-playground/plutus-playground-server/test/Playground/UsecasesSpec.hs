{-# LANGUAGE OverloadedStrings #-}

module Playground.UsecasesSpec
    ( spec
    ) where

import           Control.Monad.IO.Class (liftIO)
import qualified Data.Aeson             as JSON
import qualified Data.ByteString.Char8  as BSC
import           Data.Either            (isRight)
import           Data.Swagger.Internal  (Schema)
import qualified Data.Text              as Text
import           Ledger.Types           (Blockchain, Value)
import           Playground.API         (Evaluation (Evaluation), Expression (Action, Wait), Fn (Fn), FunctionSchema,
                                         PlaygroundError, SourceCode (SourceCode))
import qualified Playground.Interpreter as PI
import           Playground.Server      (mkInterpreterInstance, runInterpreterInstance)
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
                  [JSON.String "{\"vestingTranche1\":{\"vestingTrancheDate\":{\"getHeight\":1},\"vestingTrancheAmount\":{\"getValue\":1}},\"vestingTranche2\":{\"vestingTrancheDate\":{\"getHeight\":1},\"vestingTrancheAmount\":{\"getValue\":1}},\"vestingOwner\":{\"getPubKey\":1}}"
                  , JSON.String "{\"getValue\": 1}"
                  ]
            ]
            (sourceCode vesting)
            []

gameSpec :: Spec
gameSpec =
    describe "game" $
    it "should compile" $ compile game >>= (`shouldSatisfy` isRight)

messagesSpec :: Spec
messagesSpec =
    describe "messages" $
    it "should compile" $ compile messages >>= (`shouldSatisfy` isRight)

crowdfundingSpec :: Spec
crowdfundingSpec =
    describe "crowdfunding" $
    it "should compile" $ compile crowdfunding >>= (`shouldSatisfy` isRight)

sourceCode :: BSC.ByteString -> SourceCode
sourceCode = SourceCode . Text.pack . BSC.unpack

compile :: BSC.ByteString -> IO (Either PlaygroundError [FunctionSchema Schema])
compile usecase = do
    interpreter <- mkInterpreterInstance
    liftIO . runInterpreterInstance interpreter . PI.compile . sourceCode $
        usecase

evaluate ::
       Evaluation
    -> IO (Either PlaygroundError ( Blockchain
                                  , [EmulatorEvent]
                                  , [(Wallet, Value)]))
evaluate evaluation = do
    interpreter <- mkInterpreterInstance
    liftIO . runInterpreterInstance interpreter $ PI.runFunction evaluation
