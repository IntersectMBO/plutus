module Marlowe.ParserTests where

import Prelude
import Control.Monad.Reader (runReaderT)
import Data.Either (Either(..))
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), stripPrefix, stripSuffix, trim)
import Marlowe.Gen (genContract)
import Marlowe.GenWithHoles (GenWithHoles, unGenWithHoles)
import Marlowe.Holes (Contract)
import Marlowe.Parser (parseContract)
import Test.QuickCheck (class Testable, Result, (===))
import Test.Unit (Test, TestSuite, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Pretty (genericPretty)

all :: TestSuite
all =
  suite "Marlowe.Parser" do
    test "Contract Parser" $ quickCheckGen contractParser
    test "Pretty Contract Parser" $ quickCheckGen prettyContractParser

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) false

contractParser :: GenWithHoles Result
contractParser = do
  v <- genContract
  let
    contractWithNoParens = fromMaybe (show v) (stripPrefix (Pattern "(") (show v) >>= stripSuffix (Pattern ")"))

    result = parseContract contractWithNoParens

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)

prettyContractParser :: GenWithHoles Result
prettyContractParser = do
  v <- genContract
  let
    prettyContract = trim <<< show <<< genericPretty $ v

    contractWithNoParens = fromMaybe prettyContract (stripPrefix (Pattern "(") prettyContract >>= stripSuffix (Pattern ")"))

    result = parseContract contractWithNoParens

    (expected :: Either String Contract) = Right v
  pure (show result === show expected)
