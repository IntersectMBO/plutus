module BridgeTests
       ( all
       ) where

import Prelude

import AjaxUtils (decodeJson)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Core as Argonaut
import Data.Either (Either(..))
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Language.Haskell.Interpreter (CompilationError, InterpreterError, InterpreterResult)
import Node.FS (FS)
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency, TokenId)
import Test.Unit (TestSuite, suite, test)
import TestUtils (assertDecodesTo, equalGShow)
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
          (decodeJson (Argonaut.fromArray []) :: Either String (NonEmptyList TokenId))
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
          (Proxy :: Proxy (Either InterpreterError (InterpreterResult CompilationResult)))
          "test/compilation_response1.json"
      test "Decode an EvaluationResult." do
        assertDecodesTo
          (Proxy :: Proxy EvaluationResult)
          "test/evaluation_response1.json"
      test "Decode a CompilationError." do
        assertDecodesTo
          (Proxy :: Proxy (Array CompilationError))
          "test/evaluation_error1.json"
