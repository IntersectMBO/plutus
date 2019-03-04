module BridgeTests
       ( all
       ) where

import Prelude

import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Generic.Aeson (decodeJson)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Generic (class Generic)
import Language.Haskell.Interpreter (CompilationError)
import Node.Encoding (Encoding(UTF8))
import Node.FS (FS)
import Node.FS.Sync as FS
import Playground.API (CompilationResult, EvaluationResult)
import Test.Unit (TestSuite, Test, failure, success, suite, test)

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Bridge" do
    jsonHandling

jsonHandling :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
jsonHandling = do
    suite "Json handling" do
      test "Decode a CompilationResult." do
        compilation1 :: Either String (Either (Array CompilationError) CompilationResult) <- decodeFile "test/compilation_response1.json"
        assertRight compilation1
      test "Decode an EvaluationResult." do
        evaluation1 :: Either String EvaluationResult <- decodeFile "test/evaluation_response1.json"
        assertRight evaluation1
      test "Decode a CompilationError." do
        error1 :: Either String (Array CompilationError) <- decodeFile "test/evaluation_error1.json"
        assertRight error1

assertRight :: forall e a. Either String a -> Test e
assertRight (Left err) = failure err
assertRight (Right _) = success

decodeFile :: forall m a eff.
  MonadEff (fs :: FS, exception :: EXCEPTION | eff) m
  => Generic a
  => String
  -> m (Either String a)
decodeFile filename = do
  contents <- liftEff $ FS.readTextFile UTF8 filename
  pure (jsonParser contents >>= decodeJson)
