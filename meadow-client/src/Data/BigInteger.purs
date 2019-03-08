module Data.BigInteger (BigInteger, fromInt, fromString) where

import Prelude

import Data.BigInt (BigInt, toString)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, unwrap)
import Test.QuickCheck (class Arbitrary, arbitrary)

import Data.BigInt as BigInt

newtype BigInteger
  = BigInteger BigInt

derive instance newtypeBigInteger :: Newtype BigInteger _

derive instance genericBigInteger :: Generic BigInteger _

instance eqBigInteger :: Eq BigInteger where
  eq = genericEq

instance ordBigInteger :: Ord BigInteger where
  compare v = genericCompare v

instance showBigInteger :: Show BigInteger where
  show = toString <<< unwrap

instance arbitraryBigInteger :: Arbitrary BigInteger where
  arbitrary = map fromInt arbitrary

fromInt :: Int -> BigInteger
fromInt = BigInteger <<< BigInt.fromInt

fromString :: String -> Maybe BigInteger
fromString s = BigInteger <$> BigInt.fromString s

instance semiringBigInteger :: Semiring BigInteger where
  add a b = add a b
  zero = fromInt 0
  mul a b = mul a b
  one = fromInt 1

instance ringBigInteger :: Ring BigInteger where
  sub v = sub v

instance commutativeRingBigInteger :: CommutativeRing BigInteger

instance euclideanRingBigInteger :: EuclideanRing BigInteger where
  div a b = div a b
  mod a b = mod a b
  degree = degree <<< unwrap
