import Test.Tasty
import Test.Tasty.QuickCheck as QuickCheck
import Data.Fixed
import Data.List
-- import Test.Tasty.HUnit as HUnit
import System.Clock

instance Arbitrary TimeSpec where
  arbitrary = do
    sec <- arbitrarySizedIntegral
    nan <- arbitrarySizedIntegral
    return $ TimeSpec sec nan

main = defaultMain (adjustOption (QuickCheckTests 100000 +) $ tests)

tests :: TestTree
tests  = testGroup "All tests" [numInstanceTests, ordInstanceTests]

numInstanceTests = testGroup "Num instance tests" [qcNumInstance]
ordInstanceTests = testGroup "Ord instance tests" [qcOrdInstance]

qcNumInstance = testGroup "QuickCheck"
  [ 
    QuickCheck.testProperty "x = abs(x) * signum(x)"                                 $ \ x   -> (x :: TimeSpec) == (abs x) * (signum x)
  , QuickCheck.testProperty "integer     addition equals TimeSpec     addition"      $ \ x y -> x + y == toNanoSecs (fromInteger x + fromInteger y)
  , QuickCheck.testProperty "integer subtraction equals TimeSpec subtracttion"      $ \ x y -> x - y == toNanoSecs (fromInteger x - fromInteger y)
  , QuickCheck.testProperty "rational multiplication equals TimeSpec multiplication" $
      \ x y ->
        let rationalMul = truncate                         ((x :: Nano) *                       (y :: Nano) * (10^9))
            timespecMul = toNanoSecs (fromInteger (truncate (x * 10^9)) * fromInteger (truncate (y * 10^9)))
        in  rationalMul == timespecMul
  , QuickCheck.testProperty "neg(neg(x)) = x" $ \ x -> negate (negate x :: TimeSpec) == x
  ]

qcOrdInstance = testGroup "QuickCheck"
  [
    QuickCheck.testProperty "random list of TimeSpecs is sorted like equivalent list of integers" $ \ x -> sort (x :: [TimeSpec]) == map (fromInteger) (sort (map toNanoSecs x))
  ]
