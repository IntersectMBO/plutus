module Marlowe.ParserTests where

import Prelude

import Control.Alternative ((<|>))
import Control.Lazy (class Lazy)
import Control.Monad.Gen (class MonadGen)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (Either(..))
import Marlowe.Gen (genContract, genObservation, genValue)
import Marlowe.Parser (contract, observation, value)
import Marlowe.Pretty (pretty)
import Marlowe.Types (Contract, Observation, Value)
import Test.QuickCheck (class Testable, Result, (===))
import Test.QuickCheck.Gen (Gen)
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
    test "Contract Parser" $ quickCheckGen contractParser
    test "Pretty Contract Parser" $ quickCheckGen prettyContractParser

quickCheckGen :: forall prop. Testable prop => Gen prop -> Test
quickCheckGen = quickCheck

valueParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Result
valueParser = do
  v <- genValue
  pure (runParser (show v) (parens value <|> value) === Right v)
  
prettyValueParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Result
prettyValueParser = do
  v <- genValue
  pure (runParser (show $ pretty v) (parens value <|> value) === Right v)
  
observationParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => m Result
observationParser = do
  v <- genObservation
  pure (runParser (show v) (parens observation <|> observation) === Right v)

prettyObservationParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => m Result
prettyObservationParser = do
  v <- genObservation
  pure (runParser (show $ flatten $ pretty v) (parens observation <|> observation) === Right v)

contractParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => Lazy (m Contract) => m Result
contractParser = do
  v <- genContract
  pure (runParser (show v) (parens contract <|> contract) === Right v)

prettyContractParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => Lazy (m Contract) => m Result
prettyContractParser = do
  v <- genContract
  pure (runParser (show $ pretty v) (parens contract <|> contract) === Right v)