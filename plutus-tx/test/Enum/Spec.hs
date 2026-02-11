{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Enum.Spec (enumTests) where

import Control.Monad as HS (unless)
import Data.List qualified as HS (intercalate, nub)
import Hedgehog
import Hedgehog.Gen
import PlutusTx.Enum as Tx
import PlutusTx.Eq qualified as Tx
import PlutusTx.List qualified as Tx
import PlutusTx.Test.Golden
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog
import Prelude hiding (Eq (..), error)
import Prelude qualified as HS (Bounded (..), Enum (..), Eq (..), Show (..))

data SomeVeryLargeEnum
  = E1
  | E2
  | E3
  | E4
  | E5
  | E6
  | E7
  | E8
  | E9
  | E10
  deriving stock (HS.Eq, HS.Enum, HS.Bounded, HS.Show)
deriveEnum ''SomeVeryLargeEnum

data SomeVeryLargePhantom a b c d e f g h
  = P1
  | P2
  | P3
  | P4
  | P5
  | P6
  | P7
  | P8
  | P9
  | P10
  deriving stock (HS.Eq, HS.Enum, HS.Bounded, HS.Show)
deriveEnum ''SomeVeryLargePhantom

-- we lack Tx.Bounded so we use Haskell's for the tests
enumTests :: TestTree
enumTests =
  let
   in testGroup
        "PlutusTx.Enum tests"
        [ testProperty "no dups" prop_nodups
        , testCase "full length" $ Tx.length (Tx.enumFromTo @SomeVeryLargeEnum HS.minBound HS.maxBound) @?= Tx.fromEnum @SomeVeryLargeEnum HS.maxBound + 1
        , runTestNested
            ["test", "Enum", "Golden"]
            [ testNestedGhc
                [ $(goldenCodeGen "SomeVeryLargeEnum" (deriveEnum ''SomeVeryLargeEnum))
                , $(goldenCodeGen "SomeVeryLargePhantom" (deriveEnum ''SomeVeryLargePhantom))
                , $(goldenCodeGen "Bool" (deriveEnum ''Bool))
                , $(goldenCodeGen "Unit" (deriveEnum ''()))
                ]
            ]
        , enumFromToTests
        , enumFromThenToTests
        ]

-- we lack Tx.Bounded so we use Haskell's for the tests
prop_nodups :: Property
prop_nodups = property $ do
  from <- forAll enumBounded
  to <- forAll enumBounded
  let res = Tx.enumFromTo @SomeVeryLargeEnum from to
  HS.nub res === res

enumFromToTests :: TestTree
enumFromToTests =
  testGroup
    "enumFromTo"
    [ testCase "enumFromTo (-2) 2 == [-2..2]" $ Tx.enumFromTo @Integer (-2) 2 @?= [-2 .. 2]
    , testCase "enumFromTo 2 (-2) == []" $ Tx.enumFromTo @Integer 2 (-2) @?= []
    , testCase "enumFromTo 42 42 == [42]" $ Tx.enumFromTo @Integer 42 42 @?= [42]
    ]

enumFromThenToTests :: TestTree
enumFromThenToTests =
  testGroup
    "enumFromThenTo"
    [ testCase "enumFromThenTo 1 2 100  == [1..100]" $
        Tx.enumFromThenTo @Integer 1 2 100 @?=* [1 .. 100]
    , testCase "enumFromThenTo 1 2 100  == [1,2..100]" $
        Tx.enumFromThenTo @Integer 1 2 100 @?=* [1, 2 .. 100]
    , testCase "enumFromThenTo 100 99 1 == [100,99..1]" $
        Tx.enumFromThenTo @Integer 100 99 1 @?=* [100, 99 .. 1]
    , testCase "enumFromThenTo 100 17 (-700) == [100,17..(-700)]" $
        Tx.enumFromThenTo @Integer 100 17 (-700) @?=* [100, 17 .. (-700)]
    , testCase "enumFromThenTo 0 5 99   == [0,5..99]" $
        Tx.enumFromThenTo @Integer 0 5 99 @?=* [0, 5 .. 99]
    , testCase "enumFromThenTo 0 5 100  == [0,5..100]" $
        Tx.enumFromThenTo @Integer 0 5 100 @?=* [0, 5 .. 100]
    , testCase "enumFromThenTo 0 5 101  == [0,5..101]" $
        Tx.enumFromThenTo @Integer 0 5 101 @?=* [0, 5 .. 101]
    , testCase "enumFromThenTo 100 95 0 == [100,95..0]" $
        Tx.enumFromThenTo @Integer 100 95 0 @?=* [100, 95 .. 0]
    , testCase "enumFromThenTo 100 95 (-9) == [100,95..(-9)]" $
        Tx.enumFromThenTo @Integer 100 95 (-9) @?=* [100, 95 .. (-9)]
    , testCase "enumFromThenTo 100 95 (-10) == [100,95..(-10)]" $
        Tx.enumFromThenTo @Integer 100 95 (-10) @?=* [100, 95 .. (-10)]
    , testCase "enumFromThenTo 100 95 (-11) == [100,95..(-11)]" $
        Tx.enumFromThenTo @Integer 100 95 (-11) @?=* [100, 95 .. (-11)]
    , testCase "enumFromThenTo 42 42 41 == []" $
        Tx.enumFromThenTo @Integer 42 42 41 @?=* []
    , testCase "enumFromThenTo 42 42 42 == [42*]" $
        Tx.enumFromThenTo @Integer 42 42 42 @?=* [42, 42 .. 42]
    , testCase "enumFromThenTo 42 42 43 == [42*]" $
        Tx.enumFromThenTo @Integer 42 42 43 @?=* [42, 42 .. 43]
    , testCase "enumFromThenTo False False False == [False*]" $
        Tx.enumFromThenTo False False False @?=* [False, False .. False]
    , testCase "enumFromThenTo False False True  == [False*]" $
        Tx.enumFromThenTo False False True @?=* [False, False .. True]
    , testCase "enumFromThenTo False True  False == [False]" $
        Tx.enumFromThenTo False True False @?=* [False, True .. False]
    , testCase "enumFromThenTo False True  True  == [False,True]" $
        Tx.enumFromThenTo False True True @?=* [False, True .. True]
    , testCase "enumFromThenTo True  False False == [True,False]" $
        Tx.enumFromThenTo True False False @?=* [True, False .. False]
    , testCase "enumFromThenTo True  False True  == [True]" $
        Tx.enumFromThenTo True False True @?=* [True, False .. True]
    , testCase "enumFromThenTo True  True  False == []" $
        Tx.enumFromThenTo True True False @?=* [True, True .. False]
    , testCase "enumFromThenTo True  True  True  == [True*]" $
        Tx.enumFromThenTo True True True @?=* [True, True .. True]
    , testCase "enumFromThenTo () () () == [()*]" $
        Tx.enumFromThenTo () () () @?=* [(), () .. ()]
    ]
  where
    {- Check (approximately) that two possibly infinite lists are equal.  We can get infinite lists from
       `enumFromThenTo`, both legitimately and because of implementation errors (which are exactly
       what we're testing for here).  If we just use @?= then (a) it won't terminate if we give it
       two equal infinite lists, and (b) if it fails and one of the lists is infinite then it'll try
       to generate an infinite error message, again leading to non-termination.  To deal with this,
       if an argument has more than 1000 elements then we assume it's infinite and just include an
       initial segment in any error message, and when we're comparing two such "infinite" lists we
       just compare the first 1000 elements.  The only infinite lists that enumFromThenTo can
       generate are of the form [x,x,x,...], so this is definitely a safe strategy in this context.
     -}
    l1 @?=* l2 =
      case (possiblyInfinite l1, possiblyInfinite l2) of
        (False, False) -> l1 @?= l2
        (True, False) -> failWith (showInit l1) (show l2)
        (False, True) -> failWith (show l1) (showInit l2)
        (True, True) -> HS.unless (take 1000 l1 Tx.== take 1000 l2) (failWith (showInit l1) (showInit l2))
      where
        possiblyInfinite l = Tx.drop 1000 l Tx./= []
        showInit l = "[" ++ HS.intercalate "," (fmap show (take 5 l)) ++ ",...]"
        failWith expected actual = assertFailure ("expected: " ++ expected ++ "\n but got: " ++ actual)
