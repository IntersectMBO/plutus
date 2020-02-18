module Marlowe.ParserTests where

import Prelude
import Control.Alternative ((<|>))
import Control.Monad.Reader (runReaderT)
import Data.Either (Either(..))
import Marlowe.Gen (genAction, genContract, genObservation, genTransactionWarning, genValue)
import Marlowe.GenWithHoles (GenWithHoles, unGenWithHoles)
import Marlowe.Holes (Action, Contract, Observation, Value)
import Marlowe.Parser (action, contract, observation, transactionWarning, value)
import Marlowe.Semantics (TransactionWarning)
import Test.QuickCheck (class Testable, Result, (===))
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.StringParser (runParser)
import Text.Parsing.StringParser.Basic (parens)
import Text.Pretty (genericPretty)

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
    test "TransactionWarning Parser" $ quickCheckGen transactionWarningParser
    test "Pretty TransactionWarning Parser" $ quickCheckGen prettyTransactionWarningParser

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) false

-- NOTE: If a generated value has a hole in it, the start and end positions in that
--       hole will not be the same as when they have been parsed so we `show` the
--       results to avoid this issue
valueParser :: GenWithHoles Result
valueParser = do
  v <- genValue
  let
    result = runParser (parens value <|> value) (show v)

    (expected :: Either String Value) = Right v
  pure (show result === show expected)

prettyValueParser :: GenWithHoles Result
prettyValueParser = do
  v <- genValue
  let
    result = runParser (parens value <|> value) (show $ genericPretty v)

    (expected :: Either String Value) = Right v
  pure (show result === show expected)

observationParser :: GenWithHoles Result
observationParser = do
  v <- genObservation
  let
    result = runParser (parens observation <|> observation) (show v)

    (expected :: Either String Observation) = Right v
  pure (show result === show expected)

prettyObservationParser :: GenWithHoles Result
prettyObservationParser = do
  v <- genObservation
  let
    result = runParser (parens observation <|> observation) (show $ genericPretty v)

    (expected :: Either String Observation) = Right v
  pure (show result === show expected)

actionParser :: GenWithHoles Result
actionParser = do
  v <- genAction 5
  let
    result = runParser (parens action <|> action) (show v)

    (expected :: Either String Action) = Right v
  pure (show result === show expected)

prettyActionParser :: GenWithHoles Result
prettyActionParser = do
  v <- genAction 5
  let
    result = runParser (parens action <|> action) (show $ genericPretty v)

    (expected :: Either String Action) = Right v
  pure (show result === show expected)

contractParser :: GenWithHoles Result
contractParser = do
  v <- genContract
  let
    result = runParser (parens contract <|> contract) (show v)

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)

prettyContractParser :: GenWithHoles Result
prettyContractParser = do
  v <- genContract
  let
    result = runParser (parens contract <|> contract) (show $ genericPretty v)

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)

transactionWarningParser :: GenWithHoles Result
transactionWarningParser = do
  v <- genTransactionWarning
  let
    result = runParser transactionWarning (show v)

    (expected :: Either String TransactionWarning) = Right v
  pure (show result === show expected)

prettyTransactionWarningParser :: GenWithHoles Result
prettyTransactionWarningParser = do
  v <- genTransactionWarning
  let
    result = runParser transactionWarning (show $ genericPretty v)

    (expected :: Either String TransactionWarning) = Right v
  pure (show result === show expected)
