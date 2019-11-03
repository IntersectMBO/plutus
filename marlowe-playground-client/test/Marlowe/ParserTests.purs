module Marlowe.ParserTests where

import Prelude
import Control.Alternative ((<|>))
import Control.Monad.Reader (runReaderT)
import Data.Either (Either(..))
import Marlowe.Gen (genAction, genContract, genObservation, genValue)
import Marlowe.GenWithHoles (GenWithHoles, unGenWithHoles)
import Marlowe.Parser (Action, Contract, Observation, Value, action, contractTerm, observation, value)
import Marlowe.Pretty (pretty)
import Test.QuickCheck (class Testable, Result, (===))
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Basic (parens)
import Text.PrettyPrint.Leijen (flatten)

all :: TestSuite
all =
  suite "Marlowe.Parser" do
    test "Value Parser" $ quickCheckGen valueParser
    test "Pretty Value Parser" $ quickCheckGen prettyValueParser
    test "Observation Parser" $ quickCheckGen observationParser
    test "Pretty Observation Parser" $ quickCheckGen prettyObservationParser
    test "Action Parser" $ quickCheckGen actionParser
    test "Pretty Action Parser" $ quickCheckGen prettyActionParser
    test "Contract Parser" $ quickCheckGen contractParser
    test "Pretty Contract Parser" $ quickCheckGen prettyContractParser

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) true

-- NOTE: If a generated value has a hole in it, the start and end positions in that
--       hole will not be the same as when they have been parsed so we `show` the
--       results to avoid this issue
valueParser :: GenWithHoles Result
valueParser = do
  v <- genValue
  let
    result = runParser (show v) (parens value <|> value)

    (expected :: Either String Value) = Right v
  pure (show result === show expected)

prettyValueParser :: GenWithHoles Result
prettyValueParser = do
  v <- genValue
  let
    result = runParser (show $ pretty v) (parens value <|> value)

    (expected :: Either String Value) = Right v
  pure (show result === show expected)

observationParser :: GenWithHoles Result
observationParser = do
  v <- genObservation
  let
    result = runParser (show v) (parens observation <|> observation)

    (expected :: Either String Observation) = Right v
  pure (show result === show expected)

prettyObservationParser :: GenWithHoles Result
prettyObservationParser = do
  v <- genObservation
  let
    result = runParser (show $ flatten $ pretty v) (parens observation <|> observation)

    (expected :: Either String Observation) = Right v
  pure (show result === show expected)

actionParser :: GenWithHoles Result
actionParser = do
  v <- genAction 5
  let
    result = runParser (show v) (parens action <|> action)

    (expected :: Either String Action) = Right v
  pure (show result === show expected)

prettyActionParser :: GenWithHoles Result
prettyActionParser = do
  v <- genAction 5
  let
    result = runParser (show $ flatten $ pretty v) (parens action <|> action)

    (expected :: Either String Action) = Right v
  pure (show result === show expected)

contractParser :: GenWithHoles Result
contractParser = do
  v <- genContract
  let
    result = runParser (show v) (parens contractTerm <|> contractTerm)

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)

prettyContractParser :: GenWithHoles Result
prettyContractParser = do
  v <- genContract
  let
    result = runParser (show $ pretty v) (parens contractTerm <|> contractTerm)

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)
