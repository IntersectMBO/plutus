-- | We need to wrap BigInt in a newtype so that we can create
-- | some Class instances that BigInt doesn't have
module Data.BigInteger (BigInteger, fromInt, fromString) where

import Prelude

import Data.BigInt (BigInt, toString)
import Data.BigInt as BigInt
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, over2, unwrap)
import Marlowe.Pretty (class Pretty)
import Text.PrettyPrint.Leijen (text)

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

instance prettyBigInteger :: Pretty BigInteger where
  prettyFragment = text <<< show

fromInt :: Int -> BigInteger
fromInt = BigInteger <<< BigInt.fromInt

fromString :: String -> Maybe BigInteger
fromString s = BigInteger <$> BigInt.fromString s

instance semiringBigInteger :: Semiring BigInteger where
  add = over2 BigInteger add
  zero = fromInt 0
  mul = over2 BigInteger mul
  one = fromInt 1

instance ringBigInteger :: Ring BigInteger where
  sub = over2 BigInteger sub

instance commutativeRingBigInteger :: CommutativeRing BigInteger

instance euclideanRingBigInteger :: EuclideanRing BigInteger where
  div = over2 BigInteger div
  mod = over2 BigInteger mod
  degree = degree <<< unwrap
