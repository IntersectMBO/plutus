module Helpers.Spec.FareySpec where

import Helpers.Farey

import Test.Tasty

-- import Test.QuickCheck.Property (Result(testCase))

import Data.Ratio
import Test.Tasty.HUnit

import Test.Tasty.QuickCheck as TSQ

internalTests :: TestTree
internalTests =
  testGroup
    "Farey sequences"
    [ testCase "(17 % 20) on 64 bits" $
        findTightestRationalBounds (17 % 20) 64
          @?= ( 15679732462653118871 % 18446744073709551613
              , 15679732462653118866 % 18446744073709551607
              )
    , testCase "(17 % 20) on 4 bits" $
        findTightestRationalBounds (17 % 20) 4
          @?= (11 % 13, 6 % 7)
    , testCase "(17 % 20) on 2 bits" $
        findTightestRationalBounds (17 % 20) 2
          @?= (1 % 2, 1 % 1)
    , TSQ.testProperty "between" $ \(x :: Rational) ->
        let (a, b) = findTightestRationalBounds x 64
         in a < x && x < b
    , TSQ.testProperty "same distance" $
        TSQ.forAll (arbitrary `suchThat` (/= 0)) $ \(x :: Rational) ->
          let (p, s) = findTightestRationalBounds x 64
              (a, b) = (numerator p, denominator p)
              (c, d) = (numerator s, denominator s)
           in (a + c) * denominator x == (b + d) * numerator x
    , TSQ.testProperty "previous is close to ratio" $
        TSQ.forAll (arbitrary `suchThat` (\x -> x > 0 && x < 1)) $ \(x :: Rational) ->
          let digits = 64
              (p, _) = findTightestRationalBounds x digits
           in p + (1 % (2 ^ digits - 1)) > x
    , TSQ.testProperty "successor is close to ratio" $
        TSQ.forAll (arbitrary `suchThat` (\x -> x > 0 && x < 1)) $ \(x :: Rational) ->
          let digits = 64
              (_, s) = findTightestRationalBounds x digits
           in s - (1 % (2 ^ digits - 1)) < x
    , TSQ.testProperty "boundaries remain within 64 bits" $ \(s :: Rational) ->
        let
          domain = 64
          (prev, next) = findTightestRationalBounds s domain
          maxSize = 2 ^ domain
         in
          abs (numerator prev) < maxSize
            && abs (denominator prev) < maxSize
            && abs (numerator next) < maxSize
            && abs (denominator next) < maxSize
    ]

-- >>> findTightestRationalBounds (3650722194 % 4294967287) 32
-- (17 % 20,3650722177 % 4294967267)
