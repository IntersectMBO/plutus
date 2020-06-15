module BridgeTests
  ( all
  ) where

import Prelude
import API (RunResult)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Integral (fromIntegral)
import Data.String.Regex (replace)
import Data.String.Regex.Flags (RegexFlags(..))
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Tuple (Tuple(..))
import Data.Map as Map
import Foreign.Generic (decodeJSON, encodeJSON)
import Marlowe.Semantics (AccountId(..), Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Rational(..), Slot(..), State(..), Token(..), Value(..), ValueId(..))
import Foreign (F, MultipleErrors)
import Foreign.Class (class Decode)
import Language.Haskell.Interpreter (CompilationError)
import Node.Encoding (Encoding(UTF8))
import Node.FS.Sync as FS
import Test.Unit.Assert (equal)
import Test.Unit (TestSuite, Test, failure, success, suite, test)

all :: TestSuite
all =
  suite "JSON Serialization" do
    jsonHandling
    serializationTest

jsonHandling :: TestSuite
jsonHandling = do
  test "Json handling" do
    response1 :: F RunResult <- decodeFile "test/evaluation_response1.json"
    assertRight $ runExcept response1
    error1 :: F (Array CompilationError) <- decodeFile "test/evaluation_error1.json"
    assertRight $ runExcept error1

serializationTest :: TestSuite
serializationTest =
  test "Contract Serialization" do
    -- A simple test that runs the Escrow contract to completion
    let
      ada = Token "" ""

      alicePk = PK "deadbeef"

      aliceAcc = AccountId (fromIntegral 0) alicePk

      bobRole = Role "Bob"

      const = Constant (fromIntegral 100)

      choiceId = ChoiceId "choice" alicePk

      valueExpr = AddValue const (SubValue const (NegValue const))

      token = Token "aa" "name"

      contract =
        Assert TrueObs
          ( When
              [ Case (Deposit aliceAcc alicePk ada valueExpr)
                  ( Let (ValueId "x") valueExpr
                      (Pay aliceAcc (Party bobRole) ada (Cond TrueObs (UseValue (ValueId "x")) (UseValue (ValueId "y"))) Close)
                  )
              , Case (Choice choiceId [ Bound (fromIntegral 0) (fromIntegral 1) ])
                  ( If (ChoseSomething choiceId `OrObs` (ChoiceValue choiceId const `ValueEQ` Scale (Rational (fromIntegral 1) (fromIntegral 10)) const))
                      (Pay aliceAcc (Account aliceAcc) token (AvailableMoney aliceAcc token) Close)
                      Close
                  )
              , Case (Notify (AndObs (SlotIntervalStart `ValueLT` SlotIntervalEnd) TrueObs)) Close
              ]
              (Slot (fromIntegral 100))
              Close
          )

      state =
        State
          { accounts: Map.singleton (Tuple aliceAcc token) (fromIntegral 12)
          , choices: Map.singleton choiceId (fromIntegral 42)
          , boundValues: Map.fromFoldable [ Tuple (ValueId "x") (fromIntegral 1), Tuple (ValueId "y") (fromIntegral 2) ]
          , minSlot: (Slot $ fromIntegral 123)
          }

      json = encodeJSON contract

      jsonState = encodeJSON state
    expectedJson <- liftEffect $ FS.readTextFile UTF8 "test/contract.json"
    expectedStateJson <- liftEffect $ FS.readTextFile UTF8 "test/state.json"
    let
      rx = unsafeRegex "\\s+" (RegexFlags { global: true, ignoreCase: true, multiline: true, sticky: false, unicode: true })

      expected = replace rx "" expectedJson

      expectedState = replace rx "" expectedStateJson
    equal expected json
    equal expectedState jsonState
    equal (Right contract) (runExcept $ decodeJSON json)

assertRight :: forall a. Either MultipleErrors a -> Test
assertRight (Left err) = failure (show err)

assertRight (Right _) = success

decodeFile ::
  forall m a.
  MonadAff m =>
  Decode a =>
  String ->
  m (F a)
decodeFile filename = do
  contents <- liftEffect $ FS.readTextFile UTF8 filename
  pure (decodeJSON contents)
