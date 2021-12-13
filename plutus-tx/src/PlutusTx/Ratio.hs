{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
module PlutusTx.Ratio(
    -- * Type
    Rational
    -- * Construction
    , (%)
    , fromInteger
    , ratio
    -- * Other functionality
    , numerator
    , denominator
    , round
    , truncate
    , properFraction
    , recip
    , abs
    , negate
    , half
    , fromGHC
    , toGHC
    ) where

import PlutusTx.Base qualified as P
import PlutusTx.Bool qualified as P
import PlutusTx.Eq qualified as P
import PlutusTx.Integer (Integer)
import PlutusTx.IsData qualified as P
import PlutusTx.Lift qualified as P
import PlutusTx.Maybe qualified as P
import PlutusTx.Numeric qualified as P
import PlutusTx.Ord qualified as P

import PlutusTx.Builtins qualified as Builtins

import Data.Aeson (FromJSON (parseJSON), ToJSON (toJSON), object, withObject, (.:))
import GHC.Real qualified as Ratio
import Prelude (Ord (..), Show, (*))
import Prelude qualified as Haskell

-- | Represents an arbitrary-precision ratio.
data Rational = Rational Integer Integer
  deriving stock (
    Haskell.Eq,
    Show
    )

instance P.Eq Rational where
  {-# INLINEABLE (==) #-}
  Rational n d == Rational n' d' = n P.== n' P.&& d P.== d'

instance P.Ord Rational where
  {-# INLINEABLE compare #-}
  compare (Rational n d) (Rational n' d') = P.compare (n P.* d') (n' P.* d)
  {-# INLINEABLE (<=) #-}
  Rational n d <= Rational n' d' = (n P.* d') P.<= (n' P.* d)
  {-# INLINEABLE (>=) #-}
  Rational n d >= Rational n' d' = (n P.* d') P.>= (n' P.* d)
  {-# INLINEABLE (<) #-}
  Rational n d < Rational n' d' = (n P.* d') P.< (n' P.* d)
  {-# INLINEABLE (>) #-}
  Rational n d > Rational n' d' = (n P.* d') P.> (n' P.* d)

instance Ord Rational where
  compare (Rational n d) (Rational n' d') = compare (n * d') (n' * d)
  Rational n d <= Rational n' d' = (n * d') <= (n' * d)
  Rational n d >= Rational n' d' = (n * d') >= (n' * d)
  Rational n d < Rational n' d' = (n * d') < (n' * d)
  Rational n d > Rational n' d' = (n * d') > (n' * d)

instance P.AdditiveSemigroup Rational where
  {-# INLINEABLE (+) #-}
  Rational n d + Rational n' d' =
    let newNum = (n P.* d') P.+ (n' P.* d)
        newDen = d P.* d'
        gcd' = euclid newNum newDen
     in Rational (newNum `Builtins.quotientInteger` gcd')
                 (newDen `Builtins.quotientInteger` gcd')

instance P.AdditiveMonoid Rational where
  {-# INLINEABLE zero #-}
  zero = Rational P.zero P.one

instance P.AdditiveGroup Rational where
  {-# INLINEABLE (-) #-}
  Rational n d - Rational n' d' =
    let newNum = (n P.* d') P.- (n' P.* d)
        newDen = d P.* d'
        gcd' = euclid newNum newDen
     in Rational (newNum `Builtins.quotientInteger` gcd')
                 (newDen `Builtins.quotientInteger` gcd')

instance P.MultiplicativeSemigroup Rational where
  {-# INLINEABLE (*) #-}
  Rational n d * Rational n' d' =
    let newNum = n P.* n'
        newDen = d P.* d'
        gcd' = euclid newNum newDen
     in Rational (newNum `Builtins.quotientInteger` gcd')
                 (newDen `Builtins.quotientInteger` gcd')

instance P.MultiplicativeMonoid Rational where
  {-# INLINEABLE one #-}
  one = Rational P.one P.one

instance P.ToData Rational where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (Rational n d) = P.toBuiltinData (n, d)

instance P.FromData Rational where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData dat = case P.fromBuiltinData dat of
    P.Nothing -> P.Nothing
    P.Just (n, d) -> if d P.== P.zero
                     then Builtins.error ()
                     else P.Just (n % d)

instance P.UnsafeFromData Rational where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData dat = case P.unsafeFromBuiltinData dat of
    (n, d) -> if d P.== P.zero
              then Builtins.error ()
              else n % d

instance ToJSON Rational where
  toJSON (Rational n d) =
    object
      [ ("numerator", toJSON n)
      , ("denominator", toJSON d)
      ]

instance FromJSON Rational where
  parseJSON = withObject "Rational" Haskell.$ \obj -> do
    n <- obj .: "numerator"
    d <- obj .: "denominator"
    if d Haskell.== 0
      then Haskell.fail "Zero denominator is invalid."
      else Haskell.pure (n % d)

-- | Makes a 'Rational' from a numerator and a denominator.
--
-- = Important note
--
-- If given a zero denominator, this function will error. If you don't mind a
-- size increase, and care about safety, use 'ratio' instead.
{-# INLINEABLE (%) #-}
(%) :: Integer -> Integer -> Rational
n % d
  | d P.== P.zero = Builtins.error ()
  | d P.< P.zero = P.negate n % P.negate d
  | P.True =
    let gcd' = euclid n d
     in Rational (n `Builtins.quotientInteger` gcd')
                 (d `Builtins.quotientInteger` gcd')

infixl 7 %

-- | Safely constructs a 'Rational' from a numerator and a denominator. Returns
-- 'Nothing' if given a zero denominator.
{-# INLINEABLE ratio #-}
ratio :: Integer -> Integer -> P.Maybe Rational
ratio n d
  | d P.== P.zero = P.Nothing
  | d P.< P.zero = P.Just (P.negate n % P.negate d)
  | P.True =
    let gcd' = euclid n d
     in P.Just P..
        Rational (n `Builtins.quotientInteger` gcd') P.$
        d `Builtins.quotientInteger` gcd'

-- | Converts a 'Rational' to a GHC 'Ratio.Rational', preserving value. Does not
-- work on-chain.
toGHC :: Rational -> Ratio.Rational
toGHC (Rational n d) = n Ratio.% d

-- | Returns the (possibly reduced) numerator of its argument.
{-# INLINEABLE numerator #-}
numerator :: Rational -> Integer
numerator (Rational n _) = n

-- | Returns the (possibly reduced) denominator of its argument. This will
-- always be greater than 1, although the type does not describe this.
{-# INLINEABLE denominator #-}
denominator :: Rational -> Integer
denominator (Rational _ d) = d

-- | 0.5
{-# INLINEABLE half #-}
half :: Rational
half = Rational 1 2

-- | Converts an 'Integer' into the equivalent 'Rational'.
{-# INLINEABLE fromInteger #-}
fromInteger :: Integer -> Rational
fromInteger num = Rational num P.one

-- | Converts a GHC 'Ratio.Rational', preserving value. Does not work on-chain.
fromGHC :: Ratio.Rational -> Rational
fromGHC r = Ratio.numerator r % Ratio.denominator r

-- | Produces the additive inverse of its argument.
--
-- = Note
--
-- This is specialized for 'Rational'; use this instead of the generic version
-- of this function, as it is significantly smaller on-chain.
{-# INLINEABLE negate #-}
negate :: Rational -> Rational
negate (Rational n d) = Rational (P.negate n) d

-- | Returns the absolute value of its argument.
--
-- = Note
--
-- This is specialized for 'Rational'; use this instead of the generic version
-- of this function, as it is significantly smaller on-chain.
{-# INLINEABLE abs #-}
abs :: Rational -> Rational
abs rat@(Rational n d)
  | n P.< P.zero = Rational (P.negate n) d
  | P.True = rat

-- | @'properFraction' r@ returns the pair @(n, f)@, such that all of the
-- following hold:
--
-- * @'fromInteger' n 'P.+' f = r@;
-- * @n@ and @f@ both have the same sign as @r@; and
-- * @'abs' f 'P.<' 'P.one'@.
{-# INLINEABLE properFraction #-}
properFraction :: Rational -> (Integer, Rational)
properFraction (Rational n d) =
  (n `Builtins.quotientInteger` d,
   Rational (n `Builtins.remainderInteger` d) d)

-- | Gives the reciprocal of the argument; specifically, for @r 'P./='
-- 'P.zero'@, @r 'P.*' 'recip' r = 'P.one'@.
--
-- = Important note
--
-- The reciprocal of zero is mathematically undefined; thus, @'recip' 'P.zero'@
-- will error. Use with care.
{-# INLINEABLE recip #-}
recip :: Rational -> Rational
recip (Rational n d)
  | n P.== P.zero = Builtins.error ()
  | n P.< P.zero = Rational (P.negate d) (P.negate n)
  | P.True = Rational d n

-- | Returns the whole-number part of its argument, dropping any leftover
-- fractional part. More precisely, @'truncate' r = n@ where @(n, _) =
-- 'properFraction' r@, but is much more efficient.
{-# INLINEABLE truncate #-}
truncate :: Rational -> Integer
truncate (Rational n d) = n `Builtins.quotientInteger` d

-- | @'round' r@ returns the nearest 'Integer' value to @r@. If @r@ is
-- equidistant between two values, the even value will be given.
{-# INLINEABLE round #-}
round :: Rational -> Integer
round x =
  let (n, r) = properFraction x
      m = if r P.< P.zero then n P.- P.one else n P.+ P.one
      flag = abs r P.- half
   in if
          | flag P.< P.zero -> n
          | flag P.== P.zero -> if Builtins.modInteger n 2 P.== P.zero
                                then n
                                else m
          | P.True -> m

-- Helpers

-- Euclid's algorithm
{-# INLINEABLE euclid #-}
euclid :: Integer -> Integer -> Integer
euclid x y
  | y P.== P.zero = x
  | P.True = euclid y (x `Builtins.modInteger` y)

P.makeLift ''Rational

{- HLINT ignore -}

{- Note [Ratio]

The implementation of 'Ratio' and related functions (most importantly
'round' and Num/Ord instances) is the same as that found in 'GHC.Real',
specialised to `Integer`.

An important invariant is that the denominator is always positive. This is
enforced by

* Construction of 'Rational' numbers with '%' (the constructor of 'Ratio' is
  not exposed)
* Using `reduce` after every 'Num' operation

The 'StdLib.Spec' module has some property tests that check the behaviour of
'round', 'truncate', '>=', etc. against that of their counterparts in
'GHC.Real'.

-}

{- NOTE [Integer division operations]

Plutus Core provides built-in functions 'divideInteger', 'modInteger',
'quotientInteger' and 'remainderInteger' which are implemented as the Haskell
functions 'div', 'mod', 'quot', and 'rem' respectively.

The operations 'div' and 'mod' go together, as do 'quot' and 'rem': * DO NOT use
'div' with 'rem' or 'quot' with 'mod' *.  For most purposes users shoud probably
use 'div' and 'mod': see below for details.

For any integers a and b with b nonzero we have

  a * (a  `div` b) + a `mod` b = a
  a * (a `quot` b) + a `rem` b = a

(all operations give a "divide by zero" error if b = 0).  The analagous
identities for div/rem and quot/mod don't hold in general, and this can
lead to problems if you use the wrong combination of operations.

For positive divisors b, div truncates downwards and mod always returns a
non-negative result (0 <= a `mod` b <= b-1), which is consistent with standard
mathematical practice.  The `quot` operation truncates towards zero and `rem`
will give a negative remainder if a<0 and b>0.  If a<0 and b<0 then `mod` willl
also yield a negative result.  Results for different combinations of signs are
shown below.

-------------------------------
|   n  d | div mod | quot rem |
|-----------------------------|
|  41  5 |  8   1  |   8   1  |
| -41  5 | -9   4  |  -8  -1  |
|  41 -5 | -9  -4  |  -8   1  |
| -41 -5 |  8  -1  |   8  -1  |
-------------------------------

For many purposes (in particular if you're doing modular arithmetic),
a positive remainder is what you want.  Using 'div' and 'mod' achieves
this for positive values of b (but not for b negative, although doing
artimetic modulo a negative number would be unusual).

There is another possibility (Euclidean division) which is arguably more
mathematically correct than both div/mod and quot/rem. Given integers a and b
with b != 0, this returns numbers q and r with a = q*b+r and 0 <= r < |b|.  For
the numbers above this gives

-------------------
|   n  d |  q   r |
|-----------------|
|  41  5 |  8   1 |
| -41  5 | -9   4 |
|  41 -5 | -8   1 |
| -41 -5 |  9   4 |
-------------------

We get a positive remainder in all cases, but note for instance that the pairs
(41,5) and (-41,-5) give different results, which might be unexpected.

For a discussion of the pros and cons of various versions of integer division,
see Raymond T. Boute, "The Euclidean definition of the functions div and mod",
ACM Transactions on Programming Languages and Systems, April 1992.  (PDF at
https://core.ac.uk/download/pdf/187613369.pdf)
-}
