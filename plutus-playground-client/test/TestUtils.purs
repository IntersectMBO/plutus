module TestUtils where

import AjaxUtils as AjaxUtils
import Control.Monad.Eff.Class (class MonadEff, liftEff)
import Control.Monad.Eff.Exception (EXCEPTION)
import Data.Argonaut.Parser (jsonParser)
import Data.Either (Either(..))
import Data.Generic (class Generic, gShow)
import Node.Encoding (Encoding(UTF8))
import Node.FS (FS)
import Node.FS.Sync as FS
import Prelude (class Eq, bind, pure, ($), (<$>), (<>), (==), (>>=))
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
