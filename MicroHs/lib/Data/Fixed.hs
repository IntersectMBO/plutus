-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Fixed
-- Copyright   :  (c) Ashley Yakeley 2005, 2006, 2009
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Ashley Yakeley <ashley@semantic.org>
-- Stability   :  stable
-- Portability :  portable
-----------------------------------------------------------------------------

module Data.Fixed
(   -- * The Fixed Type
    Fixed(..), HasResolution(..),
    showFixed,
    -- ** 1\/1
    E0,Uni,
    -- ** 1\/10
    E1,Deci,
    -- ** 1\/100
    E2,Centi,
    -- ** 1\/1 000
    E3,Milli,
    -- ** 1\/1 000 000
    E6,Micro,
    -- ** 1\/1 000 000 000
    E9,Nano,
    -- ** 1\/1 000 000 000 000
    E12,Pico,
    -- * Generalized Functions on Real's
    div',
    mod',
    divMod'
) where
import Data.Coerce
import Data.Double
import Data.Floating
import Data.Fractional
import Data.Integer
import Data.Real
import Data.RealFrac
import Data.Typeable
import Data.TypeLits (KnownNat, natVal)
import MiniPrelude
import Prelude qualified ()
import Text.ParserCombinators.ReadPrec
import Text.Read.Internal
import Text.Read.Lex

default () -- avoid any defaulting shenanigans

div' :: (Real a,Integral b) => a -> a -> b
div' n d = floor (toRational n / toRational d)

divMod' :: (Real a,Integral b) => a -> a -> (b,a)
divMod' n d = (f,n - fromIntegral f * d) where
    f = div' n d

mod' :: (Real a) => a -> a -> a
mod' n d = n - fromInteger f * d where
    f = div' n d

type Fixed :: forall k . k -> Type
newtype Fixed a = MkFixed Integer
        deriving ( Eq  -- ^ @since 2.01
                 , Ord -- ^ @since 2.01
                 )

{-
tyFixed :: DataType
tyFixed = mkDataType "Data.Fixed.Fixed" [conMkFixed]

conMkFixed :: Constr
conMkFixed = mkConstr tyFixed "MkFixed" [] Prefix

-- | @since 4.1.0.0
instance (Typeable k,Typeable a) => Data (Fixed (a :: k)) where
    gfoldl k z (MkFixed a) = k (z MkFixed) a
    gunfold k z _ = k (z MkFixed)
    dataTypeOf _ = tyFixed
    toConstr _ = conMkFixed
-}

type HasResolution :: forall k . k -> Constraint
class HasResolution a where
    resolution :: p a -> Integer

instance KnownNat n => HasResolution n where
    resolution _ = natVal (Proxy :: Proxy n)

withType :: (Proxy a -> f a) -> f a
withType foo = foo Proxy

withResolution :: (HasResolution a) => (Integer -> f a) -> f a
withResolution foo = withType (foo . resolution)

instance Enum (Fixed a) where
    succ (MkFixed a) = MkFixed (succ a)
    pred (MkFixed a) = MkFixed (pred a)
    toEnum = MkFixed . toEnum
    fromEnum (MkFixed a) = fromEnum a
    enumFrom (MkFixed a) = coerce (enumFrom a)
    enumFromThen (MkFixed a) (MkFixed b) = coerce (enumFromThen a b)
    enumFromTo (MkFixed a) (MkFixed b) = coerce (enumFromTo a b)
    enumFromThenTo (MkFixed a) (MkFixed b) (MkFixed c) = coerce (enumFromThenTo a b c)

instance (HasResolution a) => Num (Fixed a) where
    (MkFixed a) + (MkFixed b) = MkFixed (a + b)
    (MkFixed a) - (MkFixed b) = MkFixed (a - b)
    fa@(MkFixed a) * (MkFixed b) = MkFixed (div (a * b) (resolution fa))
    negate (MkFixed a) = MkFixed (negate a)
    abs (MkFixed a) = MkFixed (abs a)
    signum (MkFixed a) = fromInteger (signum a)
    fromInteger i = withResolution (\res -> MkFixed (i * res))

instance (HasResolution a) => Real (Fixed a) where
    toRational fa@(MkFixed a) = toRational a / toRational (resolution fa)

instance (HasResolution a) => Fractional (Fixed a) where
    fa@(MkFixed a) / (MkFixed b) = MkFixed (div (a * resolution fa) b)
    recip fa@(MkFixed a) = MkFixed (div (res * res) a) where
        res = resolution fa
    fromRational r = withResolution (\res -> MkFixed (floor (r * toRational res)))

instance (HasResolution a) => RealFrac (Fixed a) where
    properFraction a = (i,a - fromIntegral i) where
        i = truncate a
    truncate f = truncate (toRational f)
    round f = round (toRational f)
    ceiling f = ceiling (toRational f)
    floor f = floor (toRational f)

chopZeros :: Integer -> String
chopZeros 0 = ""
chopZeros a | mod a 10 == 0 = chopZeros (div a 10)
chopZeros a = show a

showIntegerZeros :: Bool -> Int -> Integer -> String
showIntegerZeros True _ 0 = ""
showIntegerZeros chopTrailingZeros digits a = replicate (digits - length s) '0' ++ s' where
    s = show a
    s' = if chopTrailingZeros then chopZeros a else s

withDot :: String -> String
withDot "" = ""
withDot s  = '.':s

showFixed :: (HasResolution a) => Bool -> Fixed a -> String
showFixed chopTrailingZeros fa@(MkFixed a) | a < 0 = "-" ++ showFixed chopTrailingZeros (asTypeOf (MkFixed (negate a)) fa)
showFixed chopTrailingZeros fa@(MkFixed a) = show i ++ withDot (showIntegerZeros chopTrailingZeros digits fracNum) where
    res = resolution fa
    (i,d) = divMod a res
    -- enough digits to be unambiguous
    digits = ceiling (logBase 10 (fromInteger res) :: Double)
    maxnum = 10 ^ digits
    -- read floors, so show must ceil for `read . show = id` to hold. See #9240
    fracNum = divCeil (d * maxnum) res
    divCeil x y = (x + y - 1) `div` y

instance (HasResolution a) => Show (Fixed a) where
    showsPrec p n = showParen (p > 6 && n < 0) $ showString $ showFixed False n

instance (HasResolution a) => Read (Fixed a) where
    readPrec     = readNumber convertFixed
    readListPrec = readListPrecDefault
    readList     = readListDefault

convertFixed :: forall a . HasResolution a => Lexeme -> ReadPrec (Fixed a)
convertFixed (Number n)
 | Just (i, f) <- numberToFixed e n =
    return (fromInteger i + (fromInteger f / (10 ^ e)))
    where r = resolution (Proxy :: Proxy a)
          -- round 'e' up to help make the 'read . show == id' property
          -- possible also for cases where 'resolution' is not a
          -- power-of-10, such as e.g. when 'resolution = 128'
          e = ceiling (logBase 10 (fromInteger r) :: Double)
convertFixed _ = pfail

data E0

instance HasResolution E0 where
    resolution _ = 1

type Uni = Fixed E0

data E1

instance HasResolution E1 where
    resolution _ = 10

type Deci = Fixed E1

data E2

instance HasResolution E2 where
    resolution _ = 100

type Centi = Fixed E2

data E3

instance HasResolution E3 where
    resolution _ = 1000

type Milli = Fixed E3

data E6

instance HasResolution E6 where
    resolution _ = 1000000

type Micro = Fixed E6

data E9

instance HasResolution E9 where
    resolution _ = 1000000000

type Nano = Fixed E9

data E12

instance HasResolution E12 where
    resolution _ = 1000000000000

type Pico = Fixed E12
