module Marlowe.CompletionItemsTests where

import Prelude
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Either (Either, isRight)
import Data.Enum (upFromIncluding)
import Data.Map as Map
import Data.Set as Set
import Data.Traversable (traverse_)
import Marlowe.Holes (MarloweHole(..), MarloweType(..), getMarloweConstructors, marloweHoleToSuggestionText)
import Marlowe.Parser (parse)
import Marlowe.Parser as Parser
import Test.Unit (TestSuite, failure, success, suite, test)

mkHole :: MarloweType -> MarloweHole
mkHole marloweType = MarloweHole { name: mempty, range: zero, marloweType }

holeSuggestions :: Boolean -> MarloweHole -> Array String
holeSuggestions stripParens marloweHole@(MarloweHole { name, marloweType }) =
  let
    marloweHoles = getMarloweConstructors marloweType
  in
    map (marloweHoleToSuggestionText stripParens marloweHole) $ Set.toUnfoldable $ Map.keys marloweHoles

-- | For each constructor of a particular type we generate a string that might have holes in it
--   We then parse that string to ensure that we have produced something valid
mkTest :: forall a. Show a => Boolean -> MarloweType -> (String -> Either String a) -> TestSuite
mkTest stripParens marloweType parser = do
  test (show marloweType) do
    let
      items = holeSuggestions stripParens (mkHole marloweType)

      parsed = map parser items
    if Array.all isRight parsed then
      success
    else
      failure $ "expected all parsable but got " <> show parsed <> " for items " <> show items

-- | We use this testFor function in combination with `upFromIncluding bottom` in order to ensure
--   that we have written a test for every MarloweType
testFor :: MarloweType -> TestSuite
testFor ChoiceIdType = mkTest false ChoiceIdType (parse Parser.choiceId')

testFor ValueIdType = mkTest false ValueIdType (parse Parser.valueId)

testFor ActionType = mkTest false ActionType (parse Parser.action)

testFor PayeeType = mkTest false PayeeType (parse Parser.payeeExtended)

testFor CaseType = mkTest false CaseType (parse Parser.case')

testFor ValueType = mkTest false ValueType (parse (Parser.value unit))

testFor ObservationType = mkTest false ObservationType (parse Parser.observation)

testFor ContractType = mkTest false ContractType (parse Parser.contract)

testFor BoundType = mkTest false BoundType (parse Parser.bound)

testFor TokenType = mkTest false TokenType (parse Parser.token)

testFor PartyType = mkTest false PartyType (parse Parser.partyExtended)

testFor ExtendedTimeoutType = mkTest false ExtendedTimeoutType (parse Parser.extendedTimeout)

all :: TestSuite
all =
  suite "Completion Items Tests" do
    let
      (types :: Array MarloweType) = upFromIncluding bottom
    traverse_ testFor types
    -- We do an extra test for the nearley parser since it is not tested in the testFor tests
    mkTest true ContractType $ lmap show <<< Parser.parseContract
