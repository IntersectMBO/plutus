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
import Test.Unit (Test, TestSuite, failure, success, suite, test)
import Test.Unit.QuickCheck (quickCheck)
import Text.Parsing.StringParser (runParser)
import Text.Parsing.StringParser.Basic (integral)
import Text.Pretty (genericPretty)

all :: TestSuite
all =
  suite "Marlowe.Parser" do
    test "Numbers Parser" $ integralParser
    test "Contract Parser" $ quickCheckGen contractParser
    test "Pretty Contract Parser" $ quickCheckGen prettyContractParser

quickCheckGen :: forall prop. Testable prop => GenWithHoles prop -> Test
quickCheckGen g = quickCheck $ runReaderT (unGenWithHoles g) false

integralParser :: Test
integralParser = do
  -- https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#numeric-underscores
  checkParser true (runParser integral) "01_234__5_67___890"
  checkParser true (parseContract) "Let \"a\" (Constant 01_234__5_67___890) Close"
  checkParser false (runParser integral) "1000_"
  checkParser false (parseContract) "Let \"a\" (Constant 1000_) Close"
  checkParser false (runParser integral) "_1000"
  checkParser false (parseContract) "Let \"a\" (Constant _1000) Close"
  checkParser false (runParser integral) "-_1000"
  checkParser false (parseContract) "Let \"a\" (Constant -_1000) Close"
  where
  checkParser :: forall e r. Show e => Boolean -> (String -> Either e r) -> String -> Test
  checkParser good expr str = case expr str of
    Left err -> if good then failure (show err) else success
    Right _ -> if good then success else failure ("Number " <> str <> " should fail to parse")

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
