{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt Language.PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module Language.PlutusTx.Ratio(
    Ratio
    , Rational
    , (%)
    , fromInteger
    , numerator
    , denominator
    , round
    , truncate
    , properFraction
    , recip
    , half
    , fromGHC
    , toGHC
    -- * Misc.
    , quotRem
    , gcd
    , abs
    , reduce
    ) where

import qualified Language.PlutusTx.Bool     as P
import qualified Language.PlutusTx.Eq       as P
import qualified Language.PlutusTx.IsData   as P
import qualified Language.PlutusTx.Lift     as P
import qualified Language.PlutusTx.Numeric  as P
import qualified Language.PlutusTx.Ord      as P

import qualified Language.PlutusTx.Builtins as Builtins

import           Data.Aeson                 (FromJSON, ToJSON)
import           GHC.Generics               (Generic)
import qualified GHC.Real                   as Ratio
import           Prelude                    (Bool (True), Eq, Integer, Integral, Ord (..), Show (..), showParen,
                                             showString, (*))
import qualified Prelude                    as Haskell

data Ratio a = a :% a
    deriving stock (Eq,Generic)
    deriving anyclass (ToJSON, FromJSON)

instance  Show a => Show (Ratio a) where
    -- Adapted from Data.Ratio in the base library
    showsPrec p r = showParen (p > ratioPrec) Haskell.$
                    showString "(" Haskell..
                    showsPrec ratioPrec1 (numerator r) Haskell..
                    showString " % " Haskell..
                    showsPrec ratioPrec1 (denominator r) Haskell..
                    showString ")"
       where ratioPrec = 7  -- This refers to the operator precedence level of %
             ratioPrec1 = ratioPrec Haskell.+ 1

{-# ANN module "HLint: ignore" #-}

{- Note [Ratio]

The implementation of 'Ratio' and related functions (most importantly
'round' and Num/Ord instances) is the same as that found in 'GHC.Real',
specialised to `Integer` and accounting for the fact that there is no
primitive `quot` operation in Plutus.

An important invariant is that the denominator is always positive. This is
enforced by

* Construction of 'Rational' numbers with '%' (the constructor of 'Ratio' is
  not exposed)
* Using `reduce` after every 'Num' operation

The 'StdLib.Spec' module has some property tests that check the behaviour of
'round', 'truncate', '>=', etc. against that of their counterparts in
'GHC.Real'.

-}

type Rational = Ratio Integer

instance  (Integral a)  => Ord (Ratio a)  where
    (x:%y) <= (x':%y')  =  x * y' <= x' * y
    (x:%y) <  (x':%y')  =  x * y' <  x' * y

instance P.Eq a => P.Eq (Ratio a) where
    {-# INLINABLE (==) #-}
    (n1 :% d1) == (n2 :% d2) = n1 P.== n2 P.&& d1 P.== d2

instance P.AdditiveSemigroup (Ratio Integer) where
    {-# INLINABLE (+) #-}
    (x :% y) + (x' :% y') = reduce ((x P.* y') P.+ (x' P.* y)) (y P.* y')

instance P.AdditiveMonoid (Ratio Integer) where
    {-# INLINABLE zero #-}
    zero = P.zero :% P.one

instance P.AdditiveGroup (Ratio Integer) where
    {-# INLINABLE (-) #-}
    (x :% y) - (x' :% y') = reduce ((x P.* y') P.- (x' P.* y)) (y P.* y')

instance P.MultiplicativeSemigroup (Ratio Integer) where
    {-# INLINABLE (*) #-}
    (x :% y) * (x' :% y') = reduce (x P.* x') (y P.* y')

instance P.MultiplicativeMonoid (Ratio Integer) where
    {-# INLINABLE one #-}
    one = 1 :% 1

instance P.Ord (Ratio Integer) where
    {-# INLINABLE (<=) #-}
    (x :% y) <= (x' :% y') = x P.* y' P.<= (x' P.* y)

{-# INLINABLE (%) #-}
-- | Forms the ratio of two integral numbers.
(%) :: Integer -> Integer -> Ratio Integer
x % y = reduce (x P.* signum y) (abs y)

-- | Reciprocal fraction
recip :: Ratio Integer -> Ratio Integer
recip (x :% y) = (y :% x)

-- | Convert an 'Interger' to a 'Rational'
fromInteger :: Integer -> Ratio Integer
fromInteger n = n :% 1

-- | Convert a 'Data.Ratio.Rational' to a
--   Plutus-compatible 'Language.PlutusTx.Ratio.Rational'
fromGHC :: Ratio.Rational -> Ratio Integer
fromGHC (n Ratio.:% d) = n :% d

-- | Convert a 'Language.PlutusTx.Ratio.Rational' to a
--   'Data.Ratio.Rational'
toGHC :: Rational -> Ratio.Rational
toGHC (n :% d) = n Ratio.:% d

{-# INLINABLE numerator #-}
-- | Extract the numerator of the ratio in reduced form: the numerator and denominator have no common factor and the denominator is positive.
numerator :: Ratio a -> a
numerator (n :% _) = n

{-# INLINABLE denominator #-}
-- | Extract the denominator of the ratio in reduced form: the numerator and denominator have no common factor and the denominator is positive.
denominator :: Ratio a -> a
denominator (_ :% d) = d

{-# INLINABLE gcd #-}
-- From GHC.Real
-- | @'gcd' x y@ is the non-negative factor of both @x@ and @y@ of which
-- every common factor of @x@ and @y@ is also a factor; for example
-- @'gcd' 4 2 = 2@, @'gcd' (-4) 6 = 2@, @'gcd' 0 4@ = @4@. @'gcd' 0 0@ = @0@.
gcd :: Integer -> Integer -> Integer
gcd a b = gcd' (abs a) (abs b) where
    gcd' a' b'
        | b' P.== P.zero = a'
        | True           = gcd' b' (a' `Builtins.remainderInteger` b')

{-# INLINABLE truncate #-}
-- | truncate @x@ returns the integer nearest @x@ between zero and @x@
truncate :: Ratio Integer -> Integer
truncate r = let (m, _ :: Rational) = properFraction r in m

{-# INLINABLE properFraction #-}
-- From GHC.Real
-- | The function 'properFraction' takes a real fractional number @x@
-- and returns a pair @(n,f)@ such that @x = n+f@, and:
--
-- * @n@ is an integral number with the same sign as @x@; and
--
-- * @f@ is a fraction with the same type and sign as @x@,
--   and with absolute value less than @1@.
--
-- The default definitions of the 'ceiling', 'floor', 'truncate'
-- and 'round' functions are in terms of 'properFraction'.
properFraction :: Ratio Integer -> (Integer, Ratio Integer)
properFraction (n :% d) = (q, r :% d) where (q, r) = quotRem n d

{-# INLINABLE quot #-}
quot :: Integer -> Integer -> Integer
quot x y = let (q, _ :: Integer) = quotRem x y in q

{-# INLINABLE quotRem #-}
-- | simultaneous quot and rem
quotRem :: Integer -> Integer -> (Integer, Integer)
quotRem x y =
    -- `quot` is integer division truncated towards 0, while the result of `div`
    -- is truncated toward negative inf.
    -- Cf. https://stackoverflow.com/questions/339719/when-is-the-difference-between-quotrem-and-divmod-useful
    -- So we need to add 1 in some cases!
    let d   = x `Builtins.divideInteger` y
        rem = x `Builtins.remainderInteger` y
    in if d P.< P.zero P.&& rem P./= P.zero
       then (d P.+ P.one, rem)
       else (d, rem)

{-# INLINABLE half #-}
-- | 0.5
half :: Ratio Integer
half = 1 :% 2

{-# INLINABLE reduce #-}
-- | From GHC.Real
-- | 'reduce' is a subsidiary function used only in this module.
-- It normalises a ratio by dividing both numerator and denominator by
-- their greatest common divisor.
reduce :: Integer -> Integer -> Ratio Integer
reduce x y
    | y P.== 0 = Builtins.error ()
    | True     =
        let d = gcd x y in
        (x `quot` d) :% (y `quot` d)

{-# INLINABLE abs #-}
abs :: (P.Ord n, P.AdditiveGroup n) => n -> n
abs x = if x P.< P.zero then P.negate x else x

{-# INLINABLE signumR #-}
signumR :: Rational -> Rational
signumR (n :% d) = signum (n P.* d) :% 1

{-# INLINABLE signum #-}
signum :: Integer -> Integer
signum r =
    if r P.== 0
    then P.zero
    else if r P.> 0
         then P.one
         else P.negate P.one

{-# INLINABLE even #-}
even :: Integer -> Bool
even x = (x `Builtins.remainderInteger` 2) P.== P.zero

{-# INLINABLE round #-}
-- | From GHC.Real
-- | @round x@ returns the nearest integer to @x@; the even integer if @x@ is equidistant between two integers
round :: Ratio Integer -> Integer
round x
    | sig P.== P.negate P.one = n
    | sig P.== P.zero         = if even n then n else m
    | sig P.== P.one          = m
    | True                    = Builtins.error()
    where (n, r) = properFraction x
          m      = if r P.< P.zero then n P.- P.one else n P.+ P.one
          sig    = signumR (abs r P.- half)

P.makeLift ''Ratio
P.makeIsData ''Ratio
