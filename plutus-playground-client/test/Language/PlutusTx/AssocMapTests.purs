module Language.PlutusTx.AssocMapTests
       ( all
       ) where

import Prelude

import Data.Tuple.Nested
import Language.PlutusTx.AssocMap (fromTuples, unionWith)
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.QuickCheck (quickCheck)

all :: TestSuite
all =
  suite "Language.PlutusTx.AssocMap" do
    unionWithTests

unionWithTests :: TestSuite
unionWithTests = do
  suite "unionWith" do
    let a = fromTuples [ "a" /\ 1
                       , "b" /\ 2
                       , "c" /\ 3
                       ]
    let b = fromTuples [ "b" /\ 1
                       , "c" /\ 2
                       , "d" /\ 3
                       ]
    test "Merge with (+)" do
      equal
        (fromTuples [ "a" /\ 1
                    , "b" /\ 3
                    , "c" /\ 5
                    , "d" /\ 3
                    ])
        (unionWith (+) a b)
    test "Merge with (-)" do
      equal
        (fromTuples [ "a" /\ 1
                    , "b" /\ 1
                    , "c" /\ 1
                    , "d" /\ 3
                    ])
        (unionWith (-) a b)
