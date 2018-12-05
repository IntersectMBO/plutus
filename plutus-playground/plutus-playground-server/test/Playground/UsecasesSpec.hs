module Playground.UsecasesSpec
    ( spec
    ) where

import           Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString.Char8  as BSC
import           Data.Either            (isRight)
import           Data.Swagger.Internal  (Schema)
import qualified Data.Text              as Text
import           Playground.API         (FunctionSchema, PlaygroundError, SourceCode (SourceCode))
import qualified Playground.Interpreter as PI
import           Playground.Server      (mkInterpreterInstance, runInterpreterInstance)
import           Playground.Usecases    (crowdfunding, game, messages, vesting)
import           Test.Hspec             (Spec, describe, it, shouldBe, shouldSatisfy)

spec :: Spec
spec = do
    vestingSpec
    gameSpec
    messagesSpec
    crowdfundingSpec

vestingSpec :: Spec
vestingSpec =
    describe "vesting" $
    it "should compile" $ compile vesting >>= (`shouldSatisfy` isRight)

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

compile :: BSC.ByteString -> IO (Either PlaygroundError [FunctionSchema Schema])
compile usecase = do
    interpreter <- mkInterpreterInstance
    liftIO $
        runInterpreterInstance interpreter $
        PI.compile $ SourceCode . Text.pack . BSC.unpack $ usecase
