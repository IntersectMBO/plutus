-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}

module Helpers.Spec.IntervalSpec where

import Helpers.Intervals
import Test.Tasty

-- import Test.QuickCheck.Property (Result(testCase))
import Data.List (foldl')
import Data.Ratio
import Helpers.TestBuilders
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as TSQ

-- NOTE: if you want to use rationals the test name won't
-- be guaranteed to be the same, since the show instance of
-- rationals is simplified
intervalTest :: (Num a, Ord a, Show a) => (a, a) -> [RangeConstraint a] -> [(Boundary a, Boundary a)] -> TestTree
intervalTest domain' constraints expected =
  testCase testStr $
    gapsWithinRange domain' constraints
      @?= expected
  where
    testStr = inputStr ++ " => " ++ expectedStr
    inputStr = removeLastAnd $ foldl' f "not: " constraints
    f acc (NL a) = acc ++ "(< " ++ show a ++ ") && "
    f acc (NG a) = acc ++ "( > " ++ show a ++ ") && "
    f acc (NEQ a) = acc ++ "(!= " ++ show a ++ ") && "
    f acc (NLEQ a) = acc ++ "(<= " ++ show a ++ ") && "
    f acc (NGEQ a) = acc ++ "(>= " ++ show a ++ ") && "
    removeLastAnd = reverse . drop 4 . reverse

    expectedStr = removeLastOr $ foldl g "" expected
    g acc (Open a, Open b) = acc ++ "(" ++ show a ++ "," ++ show b ++ ") | "
    g acc (Open a, Closed b) = acc ++ "(" ++ show a ++ "," ++ show b ++ "] | "
    g acc (Closed a, Open b) = acc ++ "[" ++ show a ++ "," ++ show b ++ ") | "
    g acc (Closed a, Closed b) = acc ++ "[" ++ show a ++ "," ++ show b ++ "] | "
    removeLastOr = reverse . drop 3 . reverse

internalTests :: TestTree
internalTests =
  testGroup
    "Tools: Intervals"
    [ testGroup
        "gapsWithinRange"
        [ testCase "no constraint gives back the full domain " $
            gapsWithinRange' [] @?= [(Closed negInf, Closed 10)]
        , testCase "no less than 1 => [1,inf] " $
            gapsWithinRange' [NL 1] @?= [(Closed 1, Closed 10)]
        , testCase "not less than 1 and not greater than 5 => [1,5]" $
            gapsWithinRange' [NL 1, NG 5] @?= [(Closed 1, Closed 5)]
        , testCase "not less than 1, not greater than 5 and not equal to 0 => [1,5]" $
            gapsWithinRange' [NL 1, NG 5, NEQ 0] @?= [(Closed 1, Closed 5)]
        , testCase "not less than 3, not greater than 6 and not less than 0 => [3,6]" $
            gapsWithinRange' [NL 3, NG 6, NL 0] @?= [(Closed 3, Closed 6)]
        , testCase "not less then 1 and not greater than 5 and equal to 0 => []" $
            gapsWithinRange' ([NL 1, NG 5] ++ negateRange (NEQ 0)) @?= []
        , testCase "not less then 1 and not greater than 5 and equal to 3 => [3,3]" $
            gapsWithinRange' ([NL 1, NG 5] ++ negateRange (NEQ 3)) @?= [(Closed 3, Closed 3)]
        , testCase "not equal to 0 => [-inf,0) | (0,+inf]" $
            gapsWithinRange' ([NL 1, NG 5] ++ negateRange (NEQ 3)) @?= [(Closed 3, Closed 3)]
        , intervalTest @Integer (-10000, 10000) [NL 3125, NG 6250, NEQ 0, NL 0] [(Closed 3125, Closed 6250)]
        , intervalTest @Integer (-10000, 10000) [NG 6250, NEQ 0, NL 0] [(Open 0, Closed 6250)]
        , intervalTest @Integer (-10000, 10000) [NL 1, NG 3, NEQ 2] [(Closed 1, Open 2), (Open 2, Closed 3)]
        , intervalTest @Integer
            (-10000, 10000)
            [NL 1, NG 10, NEQ 2, NEQ 4, NEQ 8]
            [(Closed 1, Open 2), (Open 2, Open 4), (Open 4, Open 8), (Open 8, Closed 10)]
        , intervalTest @Integer (-10000, 10000) [NL 10, NG 9] []
        , testCase "not: (< 1 % 10) && (> 10 % 10) => [1 % 10, 1 % 1]" $
            gapsWithinRange @Rational (-1, 3) [NL (1 % 10), NG (10 % 10)] @?= [(Closed (1 % 10), Closed (1 % 1))]
        , TSQ.testProperty "[NL (1 % 10), NG (10 % 10) ] should generate within the boundaries" $
            TSQ.forAll (rationalGenerator [NL (1 % 10), NG (10 % 10)]) $
              \x -> x >= 1 % 10 && x <= 1
        , testCase "[NL (50 % 100), NG (100 % 100), NL (65 % 100) , NG (90 % 100) ]  => [65 % 100, 90 % 100]" $
            gapsWithinRange @Rational (-1, 1) [NL (50 % 100), NG (100 % 100), NL (65 % 100), NG (90 % 100)]
              @?= [(Closed (65 % 100), Closed (90 % 100))]
        , TSQ.testProperty "[NL (50 % 100), NG (100 % 100), NL (65 % 100) , NG (90 % 100) ] should generate within the boundaries" $
            TSQ.forAll (rationalGenerator [NL (50 % 100), NG (100 % 100), NL (65 % 100), NG (90 % 100)]) $
              \x -> x >= 65 % 100 && x <= 90 % 100
        , TSQ.testProperty "rationals should be generated within the boundaries" $
            TSQ.forAll (choose' @Rational (0, 1)) $
              \x -> x >= 0 && x <= 100
        ]
    ]
  where
    rationalGenerator = generateFromIntervals . gapsWithinRange @Rational (-1, 3)
    gapsWithinRange' = gapsWithinRange @Integer domain'
    domain' = (negInf, posInf)
    negInf = -10
    posInf = 10
