module BridgeTests
       ( all
       ) where

import Prelude

import AjaxUtils (ourDecodeJson)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Core as Argonaut
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Generic (class Generic, gShow)
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Language.Haskell.Interpreter (CompilationError)
import Node.Encoding (Encoding(UTF8))
import Node.FS (FS)
import Node.FS.Sync as FS
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency, TokenId)
import Test.Unit (TestSuite, Test, failure, success, suite, test)
import Type.Proxy (Proxy(..))

all :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
all =
  suite "Bridge" do
    jsonHandling

jsonHandling :: forall eff. TestSuite (exception :: EXCEPTION, fs :: FS, random :: RANDOM | eff)
jsonHandling = do
    suite "Json handling" do
      test "Decode a List." do
        assertDecodesTo
          (Proxy :: Proxy (List TokenId))
          "test/token_ids.json"
      test ("Decode an empty NonEmptyList.") do
        equalGShow
          (Left "List is empty, expecting non-empty")
          (ourDecodeJson (Argonaut.fromArray []) :: Either String (NonEmptyList TokenId))
      test ("Decode a populated NonEmptyList.") do
        assertDecodesTo
          (Proxy :: Proxy (NonEmptyList TokenId))
          "test/token_ids.json"
      test "Decode a KnownCurrency." do
        assertDecodesTo
          (Proxy :: Proxy KnownCurrency)
          "test/known_currency.json"
      test "Decode a CompilationResult." do
        assertDecodesTo
          (Proxy :: Proxy (Either (Array CompilationError) CompilationResult))
          "test/compilation_response1.json"
      test "Decode an EvaluationResult." do
        assertDecodesTo
          (Proxy :: Proxy EvaluationResult)
          "test/evaluation_response1.json"
      test "Decode a CompilationError." do
        assertDecodesTo
          (Proxy :: Proxy (Array CompilationError))
          "test/evaluation_error1.json"

equalGShow :: forall eff a. Eq a => Generic a => a -> a -> Test eff
equalGShow expected actual =
  if expected == actual then success
  else failure $ "expected " <> gShow expected <>
       ", got " <> gShow actual

assertRight :: forall e a. Either String a -> Test e
assertRight (Left err) = failure err
assertRight (Right _) = success

assertDecodesTo :: forall eff a. Generic a => Proxy a -> String -> Test (fs :: FS, exception :: EXCEPTION | eff)
assertDecodesTo proxy filename = do
  result :: Either String a <- decodeFile filename
  assertRight result

decodeFile :: forall m a eff.
  MonadEff (fs :: FS, exception :: EXCEPTION | eff) m
  => Generic a
  => String
  -> m (Either String a)
decodeFile filename = do
  contents <- liftEff $ FS.readTextFile UTF8 filename
  pure (jsonParser contents >>= ourDecodeJson)
