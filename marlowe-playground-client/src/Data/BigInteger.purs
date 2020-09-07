-- | We need to wrap BigInt in a newtype so that we can create
-- | some Class instances that BigInt doesn't have
module Data.BigInteger (BigInteger, fromInt, fromString, quot, rem) where

import Data.BigInt (BigInt, toString)
import Data.BigInt as BigInt
import Data.Integral (class Integral)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, over, over2, unwrap, wrap)
import Data.Num (class Num, abs, negate, signum)
import Data.Real (class Real, toRational)
import Foreign (ForeignError(..), fail)
import Foreign.Class (class Encode, class Decode, decode, encode)
import Prelude (class CommutativeRing, class Eq, class EuclideanRing, class Ord, class Ring, class Semiring, class Show, add, degree, div, mod, mul, pure, show, sub, (<$>), (<<<), (=<<), (>>>))
import Text.Pretty (class Args, class Pretty, text)

newtype BigInteger
  = BigInteger BigInt

derive instance newtypeBigInteger :: Newtype BigInteger _

derive newtype instance eqBigInteger :: Eq BigInteger

derive newtype instance ordBigInteger :: Ord BigInteger

instance encodeJsonBigInteger :: Encode BigInteger where
  encode (BigInteger a) = encode (toString a)

instance decodeJsonBigInteger :: Decode BigInteger where
  decode a =
    ( \x -> case BigInt.fromString x of
        Just v -> pure (BigInteger v)
        Nothing -> fail (ForeignError "Not a number")
    )
      =<< decode a

instance showBigInteger :: Show BigInteger where
  show = toString <<< unwrap

instance prettyBigInteger :: Pretty BigInteger where
  pretty = text <<< show

instance hasArgsBigInteger :: Args BigInteger where
  hasArgs _ = false
  hasNestedArgs _ = false

fromInt :: Int -> BigInteger
fromInt = BigInteger <<< BigInt.fromInt

fromString :: String -> Maybe BigInteger
fromString s = BigInteger <$> BigInt.fromString s

-- | Truncating integer division
quot :: BigInteger -> BigInteger -> BigInteger
quot = over2 BigInteger BigInt.quot

-- | The remainder after truncating integer division
rem :: BigInteger -> BigInteger -> BigInteger
rem = over2 BigInteger BigInt.rem

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

instance integralBigInteger :: Integral BigInteger where
  toBigInt = unwrap

instance realBigInteger :: Real BigInteger where
  toRational = unwrap >>> toRational

instance numBigInteger :: Num BigInteger where
  negate = over BigInteger negate
  abs = over BigInteger abs
  signum = over BigInteger signum
  fromBigInt = wrap
