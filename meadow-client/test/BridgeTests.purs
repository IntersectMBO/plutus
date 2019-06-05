module BridgeTests
       ( all
       ) where

import Prelude

import API (RunResult)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Foreign (F, MultipleErrors)
import Foreign.Class (class Decode)
import Foreign.Generic (decodeJSON)
import Language.Haskell.Interpreter (CompilationError)
import Node.Encoding (Encoding(UTF8))
import Node.FS.Sync as FS
import Test.Unit (TestSuite, Test, failure, success, suite, test)

all :: TestSuite
all =
  suite "Bridge" do
    jsonHandling

jsonHandling :: TestSuite
jsonHandling = do
    test "Json handling" do
      response1 :: F RunResult <- decodeFile "test/evaluation_response1.json"
      let r = runExcept response1
      assertRight r
      error1 :: F (Array CompilationError) <- decodeFile "test/evaluation_error1.json"
      let e = runExcept error1
      assertRight e

assertRight :: forall a. Either MultipleErrors a -> Test
assertRight (Left err) = failure (show err)
assertRight (Right _) = success

decodeFile :: forall m a.
  MonadAff m
  => Decode a
  => String
  -> m (F a)
decodeFile filename = do
  contents <- liftEffect $ FS.readTextFile UTF8 filename
  pure (decodeJSON contents)
