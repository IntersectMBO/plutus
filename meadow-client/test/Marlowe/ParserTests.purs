module Marlowe.ParserTests where

import Prelude

import Control.Alternative ((<|>))
import Control.Lazy (class Lazy)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Random (RANDOM)
import Control.Monad.Gen (class MonadGen)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (Either(..))
import Marlowe.Gen (genContract, genObservation, genValue)
import Marlowe.Parser (contract, observation, value)
import Semantics (Contract, Observation, Value)
import Test.QuickCheck (class Testable, Result, (===))
import Test.QuickCheck.Gen (Gen)
import Test.Unit (TestSuite, Test, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.Simple (parens, parse)

all :: forall eff. TestSuite (exception :: EXCEPTION, random :: RANDOM | eff)
all =
  suite "Marlowe.Parser" do
    test "Value Parser" $ quickCheckGen valueParser
    test "Observation Parser" $ quickCheckGen observationParser
    test "Contract Parser" $ quickCheckGen contractParser

quickCheckGen :: forall e prop. Testable prop => Gen prop -> Test ( random ∷ RANDOM | e )
quickCheckGen = quickCheck

valueParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => m Result
valueParser = do
  v <- genValue
  pure (parse (parens value <|> value) (show v) === Right v)
  
observationParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => m Result
observationParser = do
  v <- genObservation
  pure (parse (parens observation <|> observation) (show v) === Right v)

contractParser :: forall m. MonadGen m => MonadRec m => Lazy (m Value) => Lazy (m Observation) => Lazy (m Contract) => m Result
contractParser = do
  v <- genContract
  pure (parse (parens contract <|> contract) (show v) === Right v)