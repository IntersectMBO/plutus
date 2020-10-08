module BridgeTests
  ( all
  ) where

import Prelude
import Control.Monad.Except (runExcept)
import Data.BigInteger (fromInt)
import Data.Either (Either(..))
import Data.Map as Map
import Data.String.Regex (replace)
import Data.String.Regex.Flags (RegexFlags(..))
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Foreign (F, MultipleErrors)
import Foreign.Class (class Decode)
import Foreign.Generic (decodeJSON, encodeJSON)
import Language.Haskell.Interpreter (CompilationError)
import Marlowe.Semantics (Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Observation(..), Party(..), Payee(..), Rational(..), Slot(..), State(..), Token(..), Value(..), ValueId(..))
import Node.Encoding (Encoding(UTF8))
import Node.FS.Sync as FS
import Test.Unit (TestSuite, Test, failure, success, suite, test)
import Test.Unit.Assert (equal)

all :: TestSuite
all =
  suite "JSON Serialization" do
    jsonHandling
    serializationTest

jsonHandling :: TestSuite
jsonHandling = do
  test "Json handling" do
    response1 :: F String <- decodeFile "test/evaluation_response1.json"
    assertRight $ runExcept response1
    error1 :: F (Array CompilationError) <- decodeFile "test/evaluation_error1.json"
    assertRight $ runExcept error1

serializationTest :: TestSuite
serializationTest =
  test "Contract Serialization" do
    -- A simple test that runs the Escrow contract to completion
    let
      ada = Token "" ""

      alicePk = PK "4ecde0775d081e45f06141416cbc3afed4c44a08c93ea31281e25c8fa03548b9"

      bobRole = Role "Bob"

      const = Constant (fromInt 100)

      choiceId = ChoiceId "choice" alicePk

      valueExpr = AddValue const (SubValue const (NegValue const))

      token = Token "aa" "name"

      contract =
        Assert TrueObs
          ( When
              [ Case (Deposit alicePk alicePk ada valueExpr)
                  ( Let (ValueId "x") valueExpr
                      (Pay alicePk (Party bobRole) ada (Cond TrueObs (UseValue (ValueId "x")) (UseValue (ValueId "y"))) Close)
                  )
              , Case (Choice choiceId [ Bound (fromInt 0) (fromInt 1) ])
                  ( If (ChoseSomething choiceId `OrObs` (ChoiceValue choiceId `ValueEQ` Scale (Rational (fromInt 1) (fromInt 10)) const))
                      (Pay alicePk (Account alicePk) token (AvailableMoney alicePk token) Close)
                      Close
                  )
              , Case (Notify (AndObs (SlotIntervalStart `ValueLT` SlotIntervalEnd) TrueObs)) Close
              ]
              (Slot (fromInt 100))
              Close
          )

      state =
        State
          { accounts: Map.singleton (Tuple alicePk token) (fromInt 12)
          , choices: Map.singleton choiceId (fromInt 42)
          , boundValues: Map.fromFoldable [ Tuple (ValueId "x") (fromInt 1), Tuple (ValueId "y") (fromInt 2) ]
          , minSlot: (Slot $ fromInt 123)
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
