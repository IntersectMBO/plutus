module BridgeTests
       ( all, k
       ) where

import Prelude

import AjaxUtils (ajaxSettings)
import Control.Monad.Aff.AVar (AVAR)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Console (CONSOLE)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Generic (class Generic)
import Data.List (List)
import Data.List.Types (NonEmptyList)
import Language.Haskell.Interpreter (CompilationError)
import Node.Encoding (Encoding(UTF8))
import Node.FS (FS)
import Node.FS.Sync as FS
import Playground.API (CompilationResult, EvaluationResult, KnownCurrency, TokenId)
import Servant.PureScript.Settings (SPSettingsDecodeJson_(..), SPSettings_(..))
import Test.Unit (TestSuite, Test, failure, success, suite, test)
import Test.Unit.Console (TESTOUTPUT)
import Test.Unit.Main (runTest)
import Type.Proxy (Proxy(..))

k :: forall t57.
  Eff
    ( console :: CONSOLE
    , testOutput :: TESTOUTPUT
    , avar :: AVAR
    , exception :: EXCEPTION
    , fs :: FS
    , random :: RANDOM
    | t57
    )
    Unit
k = runTest all

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
      test ("Decode a NonEmptyList.") do
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
  let (SPSettings_ {decodeJson: SPSettingsDecodeJson_ decodeJson}) = ajaxSettings
  contents <- liftEff $ FS.readTextFile UTF8 filename
  pure (jsonParser contents >>= decodeJson)
