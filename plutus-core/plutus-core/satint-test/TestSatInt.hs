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

isArithException :: SatInt -> IO Bool
isArithException n = E.catch (n `seq` return False)
                             (\ (_ :: ArithException) -> return True)

saturatesPos :: forall a . (Integral a, Bounded a) => a -> Bool
saturatesPos n = n == maxBound

saturatesNeg :: forall a . (Integral a, Bounded a) => a -> Bool
saturatesNeg n = n == minBound

behavesOk :: (forall a. Integral a => a) -> Bool
behavesOk n =
    let
        sat = (n :: SatInt)
        int = (n :: Integer)
        lb = toInteger (minBound :: SatInt)
        ub = toInteger (maxBound :: SatInt)
    in if lb <= int && int <= ub then toInteger sat == int
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
    unitTest "1/0"     (isArithException (1 `div` 0)),
    unitTest "min*-1"  (saturatesPos ((minBound :: SatInt) * (-1))),
    unitTest "min/-1"  (saturatesNeg ((minBound :: SatInt) `div` (-1))),
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
    testProperty "rem" (propBinOp rem),
    testProperty "lcm" (propBinOp lcm),
    testProperty "gcd" (propBinOp gcd)
  ]

anyInt :: Gen Int
anyInt = choose (minBound, maxBound)

propBinOp :: (forall a. Integral a => a -> a -> a) -> Property
propBinOp (!) = forAll anyInt $ \ x ->
                forAll anyInt $ \ y ->
                property $ behavesOk (fromIntegral x ! fromIntegral y)
