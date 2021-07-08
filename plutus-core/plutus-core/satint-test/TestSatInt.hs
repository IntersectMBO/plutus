{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
-- These tests are deliberately not in the same style as our other tests, but rather mirror the tests
-- in safeint, since I want to upstream this in due course.
module Main where

import           Control.Exception                    as E
import           Data.List
import           Data.Maybe
import           Data.SatInt
import           Test.Framework                       as TF
import           Test.Framework.Providers.HUnit
import           Test.Framework.Providers.QuickCheck2
import           Test.HUnit                           as T
import           Test.QuickCheck

main :: IO ()
main = defaultMain tests

isArithException :: a -> IO Bool
isArithException n = E.catch (n `seq` return False)
                             (\ (_ :: ArithException) -> return True)

saturatesPos :: forall a . (Integral a, Bounded a) => a -> Bool
saturatesPos n = n == maxBound

saturatesNeg :: forall a . (Integral a, Bounded a) => a -> Bool
saturatesNeg n = n == minBound

behavesOk :: (forall a. Integral a => a) -> IO Bool
behavesOk n = do
    let
        sat = (n :: SatInt)
        int = (n :: Integer)
        lb = toInteger (minBound :: SatInt)
        ub = toInteger (maxBound :: SatInt)
    satThrows <- isArithException sat
    intThrows <- isArithException int
    pure $ if satThrows && intThrows then True
    else if lb <= int && int <= ub then toInteger sat == int
    else if int < lb then saturatesNeg sat
    else if int > ub then saturatesPos sat
    else False

unitTest :: Assertable t => TestName -> t -> TF.Test
unitTest msg p = testCase msg (T.assert p)

wordSize :: Int
wordSize = fromJust (find (\ n -> 2 ^ n == (0 :: Word)) [8,16,32,64,128])

tests :: [TF.Test]
tests =
  [ unitTest "0"       ((0 :: SatInt) + 0 == 0),
    unitTest "max+"    (saturatesPos ((maxBound :: SatInt) + 1)),
    unitTest "min-"    (saturatesNeg ((minBound :: SatInt) - 1)),
    unitTest "1/0"     (isArithException ((1 :: SatInt) `div` 0)),
    unitTest "min*-1"  (saturatesPos ((minBound :: SatInt) * (-1))),
    unitTest "0-min"   (saturatesPos (0 - (minBound :: SatInt))),
    unitTest "min/-1"  (saturatesPos ((minBound :: SatInt) `div` (-1))),
    unitTest "min `quot` -1"  (saturatesPos ((minBound :: SatInt) `quot` (-1))),
    unitTest "max/2*2" (((maxBound :: SatInt) `div` 2) * 2 == (maxBound :: SatInt) - 1),
    unitTest "max+min" ((maxBound :: SatInt) + (minBound :: SatInt) == -1),
    unitTest "max+*"   (saturatesPos ((2 :: SatInt) ^ (wordSize `div` 2) * 2 ^ (wordSize `div` 2 - 1))),
    unitTest "min-*"   (saturatesNeg (negate ((2 :: SatInt) ^ (wordSize `div` 2)) * 2 ^ (wordSize `div` 2 - 1))),
    testProperty "*"   (propBinOp (*)),
    testProperty "+"   (propBinOp (+)),
    testProperty "-"   (propBinOp (-)),
    testProperty "div" (propBinOp div),
    testProperty "mod" (propBinOp mod),
    testProperty "quot"(propBinOp quot),
    testProperty "rem" (propBinOp rem)
    -- lcm and gcd do *not* pass `behavesOk` since they *internally* use `abs` (which will give the wrong/saturated
    -- answer for minBound), and hence go astray after that. But we can't easily detect that this is the "correct"
    -- saturated thing to do as we do for other operations (where we can just see if the saturating version is
    -- at one of the bounds)
  ]

-- We really want to test the special cases involving combinations of -1, minBound, and maxBound. The ordinary
-- generator does *not* produce these with enough frequency to find anything.
intWithSpecialCases :: Gen Int
intWithSpecialCases = frequency [ (1, pure (-1)), (1, pure minBound), (1, pure maxBound), (80, arbitrary) ]

propBinOp :: (forall a. Integral a => a -> a -> a) -> Property
propBinOp (!) = withMaxSuccess 10000 $
                forAll intWithSpecialCases $ \ x ->
                forAll intWithSpecialCases $ \ y ->
                ioProperty $ behavesOk (fromIntegral x ! fromIntegral y)
