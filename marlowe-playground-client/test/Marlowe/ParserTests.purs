module Marlowe.ParserTests where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (fromMaybe)
import Data.String (Pattern(..), stripPrefix, stripSuffix, trim)
import Marlowe.Gen (genContract)
import Marlowe.GenWithHoles (GenWithHoles, contractQuickCheck, GenerationOptions(..))
import Marlowe.Holes (Contract)
import Marlowe.Parser (parseContract)
import Test.QuickCheck (Result, (===))
import Test.Unit (TestSuite, suite, test)
import Text.Pretty (genericPretty)

all :: TestSuite
all =
  suite "Marlowe.Parser" do
    let
      genOpts = GenerationOptions { withHoles: false, withExtendedConstructs: true }
    test "Contract Parser" $ contractQuickCheck genOpts contractParser
    test "Pretty Contract Parser" $ contractQuickCheck genOpts prettyContractParser

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
