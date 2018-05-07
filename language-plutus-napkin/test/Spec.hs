import           Hedgehog
import qualified Hedgehog.Gen        as Gen
import qualified Hedgehog.Range      as Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

main :: IO ()
main = defaultMain tests

prop_reverse :: Property
prop_reverse =
  property $ do
    xs <- forAll $ Gen.list (Range.linear 0 100) Gen.alpha
    reverse (reverse xs) === xs

tests :: TestTree
tests = testGroup "parser tests" [
   testProperty "reverse" prop_reverse
 ]
