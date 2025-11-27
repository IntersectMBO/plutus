module List.Spec (listTests) where

import PlutusTx.List qualified as PlutusTx
import PlutusTx.Ord qualified as PlutusTx

import Data.List qualified as Haskell
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog
import Prelude (Eq (..), Int, Integer, String, even, fmap, mod, odd, toInteger, ($))
import Prelude qualified as Haskell

listTests :: TestTree
listTests =
  testGroup
    "PlutusTx.List tests"
    [ testProperty "null" prop_null
    , testProperty "and" prop_and
    , testProperty "or" prop_or
    , testProperty "any" prop_any
    , testProperty "all" prop_all
    , testProperty "elem" prop_elem
    , testProperty "notElem" prop_notElem
    , testProperty "find" prop_find
    , testProperty "findIndex" prop_findIndex
    , nubByTests
    , nubTests
    , partitionTests
    , sortTests
    , sortByTests
    ]

genList :: Gen [Integer]
genList = Gen.list (Range.linear 0 10) (Gen.integral (Range.linear (-10000) 10000))

prop_null :: Property
prop_null = property $ do
  xs <- forAll genList
  PlutusTx.null xs === Haskell.null xs

prop_and :: Property
prop_and = property $ do
  xs <- fmap (fmap odd) $ forAll genList
  PlutusTx.and xs === Haskell.and xs

prop_or :: Property
prop_or = property $ do
  xs <- fmap (fmap odd) $ forAll genList
  PlutusTx.or xs === Haskell.or xs

prop_any :: Property
prop_any = property $ do
  xs <- forAll genList
  PlutusTx.any odd xs === Haskell.any odd xs

prop_all :: Property
prop_all = property $ do
  xs <- forAll genList
  PlutusTx.all odd xs === Haskell.all odd xs

prop_elem :: Property
prop_elem = property $ do
  xs <- forAll genList
  PlutusTx.elem 0 xs === Haskell.elem 0 xs

prop_notElem :: Property
prop_notElem = property $ do
  xs <- forAll genList
  PlutusTx.notElem 0 xs === Haskell.notElem 0 xs

prop_find :: Property
prop_find = property $ do
  xs <- forAll genList
  PlutusTx.find (PlutusTx.> 42) xs === Haskell.find (Haskell.> 42) xs

prop_findIndex :: Property
prop_findIndex = property $ do
  xs <- forAll genList
  PlutusTx.findIndex (PlutusTx.> 42) xs === fmap toInteger (Haskell.findIndex (Haskell.> 42) xs)

nubByTests :: TestTree
nubByTests =
  testGroup
    "nubBy"
    [ testCase "equal up to mod 3" $
        PlutusTx.nubBy (\x y -> mod x 3 == mod y 3) [1 :: Integer, 2, 4, 5, 6]
          @?= [1, 2, 6]
    ]

nubTests :: TestTree
nubTests =
  testGroup
    "nub"
    [ testCase "[] == []" $ PlutusTx.nub [] @?= ([] :: [Integer])
    , testCase "[1, 2, 2] == [1, 2]" $ PlutusTx.nub [1 :: Integer, 2, 2] @?= [1, 2]
    , testCase "[2, 1, 1] == [2, 1]" $ PlutusTx.nub [2 :: Integer, 1, 1] @?= [2, 1]
    , testCase "[1, 1, 1] == [1]" $ PlutusTx.nub [1 :: Integer, 1, 1] @?= [1]
    , testCase "[1, 2, 3, 4, 5] == [1, 2, 3, 4, 5]" $
        PlutusTx.nub [1 :: Integer, 2, 3, 4, 5] @?= [1, 2, 3, 4, 5]
    ]

partitionTests :: TestTree
partitionTests =
  testGroup
    "partition"
    [ testCase "partition \"aeiou\" \"Hello World!\"" $
        (PlutusTx.partition (`Haskell.elem` ("aeiou" :: String)) "Hello World!")
          @?= ("eoo", "Hll Wrld!")
    , testCase "partition even [1,2,3,4,5,6]" $
        (PlutusTx.partition even [1 :: Int, 2, 3, 4, 5, 6])
          @?= ([2, 4, 6], [1, 3, 5])
    ]

sortTests :: TestTree
sortTests =
  testGroup
    "sort"
    [ testCase "sort [1,6,4,3,2,5]" $
        (PlutusTx.sort [1 :: Integer, 6, 4, 3, 2, 5])
          @?= [1, 2, 3, 4, 5, 6]
    ]

sortByTests :: TestTree
sortByTests =
  testGroup
    "sortBy"
    [ testCase "sortBy second pairs" $
        ( PlutusTx.sortBy
            (\(a, _) (b, _) -> PlutusTx.compare a b)
            [(2 :: Integer, "world" :: String), (4, "!"), (1, "Hello")]
        )
          @?= [(1, "Hello"), (2, "world"), (4, "!")]
    ]
