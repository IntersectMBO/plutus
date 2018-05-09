module Main ( main
            , genPosn
            ) where

import           Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Language.PlutusCore
import           Test.Tasty
import           Test.Tasty.Hedgehog

genPosn :: MonadGen m => m AlexPosn
genPosn = AlexPn <$> int' <*> int' <*> int'
    where int' = Gen.int (Range.linear 0 1000)

main :: IO ()
main = defaultMain tests

-- TODO add unit test

prop_reverse :: Property
prop_reverse =
  property $ do
    xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
    reverse (reverse xs) === xs

tests :: TestTree
tests = testGroup "parser tests" [
   testProperty "reverse" prop_reverse
 ]
