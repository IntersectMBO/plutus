-- Unfortunately PSGenerator can't handle 'PlutusTx.Ratio' data constructor ':%',
-- so we are forced to create a mapping on PureScript side with custom 'Encode' and 'Decode' instances.
module PlutusTx.Ratio (Ratio(..), (%), reduce, numerator, denominator) where

import Data.Ratio as R
import Foreign (F, ForeignError(..), fail)
import Foreign.Class (class Decode, class Encode, encode, decode)
import Prelude

newtype Ratio a
  = Ratio (R.Ratio a)

instance showRatio :: (Show a) => Show (Ratio a) where
  show (Ratio x) = show x

instance eqRatio :: Eq a => Eq (Ratio a) where
  eq (Ratio a) (Ratio b) = eq a b

instance ordRatio :: (Ord a, EuclideanRing a) => Ord (Ratio a) where
  compare (Ratio x) (Ratio y) = compare x y

instance semiringRatio :: (Ord a, EuclideanRing a) => Semiring (Ratio a) where
  one = Ratio one
  mul (Ratio a) (Ratio b) = Ratio (mul a b)
  zero = Ratio zero
  add (Ratio a) (Ratio b) = Ratio (add a b)

instance ringRatio :: (Ord a, EuclideanRing a) => Ring (Ratio a) where
  sub (Ratio a) (Ratio b) = Ratio (sub a b)

instance commutativeRingRatio :: (Ord a, EuclideanRing a) => CommutativeRing (Ratio a)

instance euclideanRingRatio :: (Ord a, EuclideanRing a) => EuclideanRing (Ratio a) where
  degree _ = 1
  div (Ratio a) (Ratio b) = Ratio (div a b)
  mod _ _ = zero

instance divisionRingRatio :: (Ord a, EuclideanRing a) => DivisionRing (Ratio a) where
  recip (Ratio a) = Ratio (recip a)

instance encodeRatio :: (Encode a) => Encode (Ratio a) where
  encode (Ratio r) = encode [ R.numerator r, R.denominator r ]

instance decodeRatio :: (EuclideanRing a, Ord a, Decode a) => Decode (Ratio a) where
  decode value = do
    xs <- (decode value :: F (Array a))
    case xs of
      [ x, y ] -> do
        pure $ reduce x y
      _ -> fail $ ForeignError "Decoding a Ratio, expected to see an array with exactly 2 elements."

numerator :: forall a. Ratio a -> a
numerator (Ratio r) = R.numerator r

denominator :: forall a. Ratio a -> a
denominator (Ratio r) = R.denominator r

reduce :: forall a. Ord a => EuclideanRing a => a -> a -> Ratio a
reduce n d = Ratio (R.reduce n d)

infixl 7 reduce as %
