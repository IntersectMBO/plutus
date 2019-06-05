module TestUtils where

import Prelude

import Control.Monad.Except (runExcept)
import Control.Monad.Gen (class MonadGen, chooseInt, oneOf)
import Data.Bifoldable (class Bifoldable, bifoldMap)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, length)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (class GenericShow, genericShow)
import Data.List as List
import Data.List.NonEmpty (NonEmptyList(..))
import Data.NonEmpty (NonEmpty(..), (:|))
import Effect.Class (class MonadEffect, liftEffect)
import Foreign (MultipleErrors)
import Foreign.Class (class Decode, class Encode)
import Foreign.Generic (decodeJSON, encodeJSON)
import Foreign.JSON (parseJSON)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Test.QuickCheck.Gen (Gen, vectorOf)
import Test.Unit (Test, failure, success)
import Test.Unit.Assert (equal)
import Type.Proxy (Proxy)

assertRight :: forall e a. Show e => Either e a -> Test
assertRight (Left err) = failure $ show err
assertRight (Right _) = success

assertDecodesTo :: forall a. Decode a => Proxy a -> String -> Test
assertDecodesTo proxy filename = do
  result :: Either MultipleErrors a <- decodeFile filename
  assertRight result

-- | Check a value encodes to the contents of a file.
-- This test will reformat the input file to ignore any whitespace
-- differences.
assertEncodesTo :: forall a. Encode a => a -> String -> Test
assertEncodesTo value filename = do
  file <- liftEffect (FS.readTextFile UTF8 filename)
  let encoded = encodeJSON value
  let reformatted = runExcept (encodeJSON <$> parseJSON file)
  case reformatted of
    Left err -> failure $ "Input file is not valid JSON"
    Right expected -> equal expected encoded

decodeFile :: forall m a.
  MonadEffect m
  => Decode a
  => String
  -> m (Either MultipleErrors a)
decodeFile filename = do
  contents <- liftEffect $ FS.readTextFile UTF8 filename
  pure $ runExcept $ decodeJSON contents

equalWithFormatter :: forall a. Eq a => (a -> String) -> a -> a -> Test
equalWithFormatter f expected actual =
  if expected == actual then success

  else failure $ "expected " <> f expected <>
       ", got " <> f actual

-- | Similar to `equalWithFormatter`, but this instance tends to come in handy when comparing things like `Either`s.
equalWithBiformatter :: forall p a b. Bifoldable p => Eq (p a b) => (a -> String) -> (b -> String) -> p a b -> p a b -> Test
equalWithBiformatter f g = equalWithFormatter $ bifoldMap f g

equalGenericShow :: forall a rep. Eq a => Generic a rep => GenericShow rep => a -> a -> Test
equalGenericShow = equalWithFormatter genericShow

genIndex :: forall f a m. MonadGen m => Foldable f => f a -> m Int
genIndex xs = chooseInt 0 (length xs - 1)

-- | Generates an index that will either be within the array bounds, or slightly outside of it.
--
-- Useful when you want to test valid indexes, plus the edge cases,
-- but there's no point using truly random Ints and checking -1 AND
-- -1234 AND -9237581, etc.
genLooseIndex :: forall m f a. MonadGen m => Foldable f => f a -> m Int
genLooseIndex xs = chooseInt (-2) (length xs + 2)

arbitraryEither :: forall m a b. MonadGen m => m a -> m b -> m (Either a b)
arbitraryEither genLeft genRight =
  oneOf $ NonEmpty
            (Left <$> genLeft)
            [ (Right <$> genRight) ]

arbitraryNonEmptyList :: forall a. Gen a -> Gen (NonEmptyList a)
arbitraryNonEmptyList genX = do
  n <- chooseInt 0 5
  x <- genX
  xs <- List.fromFoldable <$> vectorOf n genX
  pure $ NonEmptyList $ x :| xs
