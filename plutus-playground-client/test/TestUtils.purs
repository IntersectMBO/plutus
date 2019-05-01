module TestUtils where

import Prelude

import AjaxUtils as AjaxUtils
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Gen (class MonadGen, chooseInt)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, length)
import Data.Generic (class Generic, gShow)
import Node.Encoding (Encoding(UTF8))
import Node.FS (FS)
import Node.FS.Sync as FS
import Test.Unit (Test, failure, success)
import Test.Unit.Assert (equal)
import Type.Proxy (Proxy)

assertRight :: forall e a. Either String a -> Test e
assertRight (Left err) = failure err
assertRight (Right _) = success

assertDecodesTo :: forall eff a. Generic a => Proxy a -> String -> Test (fs :: FS, exception :: EXCEPTION | eff)
assertDecodesTo proxy filename = do
  result :: Either String a <- decodeFile filename
  assertRight result

assertEncodesTo :: forall eff a. Generic a => a -> String -> Test (fs :: FS, exception :: EXCEPTION | eff)
assertEncodesTo value filename = do
  file <- jsonParser <$> liftEff (FS.readTextFile UTF8 filename)
  let encoded = AjaxUtils.encodeJson  value
  equal file (Right encoded)

decodeFile :: forall m a eff.
  MonadEff (fs :: FS, exception :: EXCEPTION | eff) m
  => Generic a
  => String
  -> m (Either String a)
decodeFile filename = do
  contents <- liftEff $ FS.readTextFile UTF8 filename
  pure (jsonParser contents >>= AjaxUtils.decodeJson)

equalWithFormatter :: forall a e. Eq a => (a -> String) -> a -> a -> Test e
equalWithFormatter f expected actual =
  if expected == actual then success

  else failure $ "expected " <> f expected <>
       ", got " <> f actual

equalGShow :: forall eff a. Eq a => Generic a => a -> a -> Test eff
equalGShow = equalWithFormatter gShow

genIndex :: forall f a m. MonadGen m => Foldable f => f a -> m Int
genIndex xs = chooseInt 0 (length xs - 1)

-- | Generates an index that will either be within the array bounds, or slightly outside of it.
--
-- Useful when you want to test valid indexes, plus the edge cases,
-- but there's no point using truly random Ints and checking -1 AND
-- -1234 AND -9237581, etc.
genLooseIndex :: forall m f a. MonadGen m => Foldable f => f a -> m Int
genLooseIndex xs = chooseInt (-2) (length xs + 2)
