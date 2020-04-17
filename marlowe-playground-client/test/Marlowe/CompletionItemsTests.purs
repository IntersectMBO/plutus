module Marlowe.CompletionItemsTests where

import Prelude
import Data.Array as Array
import Data.Either (isRight)
import Data.Map as Map
import Data.Set as Set
import Marlowe.Holes (MarloweHole(..), MarloweType(..), constructMarloweType, getMarloweConstructors)
import Marlowe.Parser (parse)
import Marlowe.Parser as Parser
import Test.Unit (TestSuite, failure, success, suite, test)
import Text.Parsing.StringParser (Parser)

mkHole :: MarloweType -> MarloweHole
mkHole marloweType = MarloweHole { name: mempty, row: zero, column: zero, marloweType }

marloweHoleToSuggestion :: MarloweHole -> String -> String
marloweHoleToSuggestion firstHole@(MarloweHole { marloweType }) constructorName =
  let
    m = getMarloweConstructors marloweType
  in
    constructMarloweType constructorName firstHole m

holeSuggestions :: MarloweHole -> Array String
holeSuggestions marloweHole@(MarloweHole { name, marloweType }) =
  let
    marloweHoles = getMarloweConstructors marloweType
  in
    map (marloweHoleToSuggestion marloweHole) $ Set.toUnfoldable $ Map.keys marloweHoles

mkTest :: forall a. Show a => MarloweType -> Parser a -> TestSuite
mkTest marloweType parser = do
  test (show marloweType) do
    let
      items = holeSuggestions (mkHole marloweType)

      parsed = map (parse parser) items
    if Array.all isRight parsed then
      success
    else
      failure $ "expected all parsable but got " <> show parsed <> " for items " <> show items

all :: TestSuite
all =
  suite "Completion Items Tests" do
    -- Note that we don't test the following because they are never used in code generation
    -- StringType
    -- BigIntegerType
    -- SlotType
    mkTest AccountIdType Parser.accountId'
    mkTest ChoiceIdType Parser.choiceId'
    mkTest ValueIdType Parser.valueId
    mkTest ActionType Parser.action
    mkTest PayeeType Parser.payee
    mkTest CaseType Parser.case'
    mkTest ValueType Parser.value
    mkTest ObservationType Parser.observation
    mkTest ContractType Parser.contract
    mkTest BoundType Parser.bound
    mkTest TokenType Parser.token
    mkTest PartyType Parser.party
