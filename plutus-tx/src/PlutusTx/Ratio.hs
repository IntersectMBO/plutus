{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=3 #-}

module PlutusTx.Ratio
  ( -- * Type
    Rational

    -- * Construction
  , unsafeRatio
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
  , gcd

    -- * Conversion from/to Haskell
  , fromHaskellRatio
  , toHaskellRatio
  , fromGHC
  , toGHC
  ) where

import PlutusTx.Applicative qualified as P
import PlutusTx.Base qualified as P
import PlutusTx.Bool qualified as P
import PlutusTx.Enum
import PlutusTx.Eq qualified as P
import PlutusTx.ErrorCodes qualified as P
import PlutusTx.Integer (Integer)
import PlutusTx.IsData qualified as P
import PlutusTx.Lift (makeLift)
import PlutusTx.Maybe qualified as P
import PlutusTx.Numeric qualified as P
import PlutusTx.Ord qualified as P
import PlutusTx.Trace qualified as P

import Data.Ratio qualified as HS
import PlutusTx.Builtins qualified as Builtins

import Control.Monad (guard)
import Data.Aeson (FromJSON (parseJSON), ToJSON (toJSON), object, withObject, (.:))
import GHC.Generics
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), HasSchemaDefinition)
import Prettyprinter (Pretty (..), (<+>))
import Prelude qualified as Haskell

{-| Represents an arbitrary-precision ratio.

The following two invariants are maintained:

1. The denominator is greater than zero.
2. The numerator and denominator are coprime. -}
data Rational = Rational Integer Integer
  deriving stock (Haskell.Eq, Haskell.Show, Generic)

makeLift ''Rational
P.deriveEq ''Rational

instance Pretty Rational where
  pretty (Rational a b) = "Rational:" <+> pretty a <+> pretty b

instance P.Ord Rational where
  {-# INLINEABLE (<=) #-}
  Rational n d <= Rational n' d' = (n P.* d') P.<= (n' P.* d)
  {-# INLINEABLE (>=) #-}
  Rational n d >= Rational n' d' = (n P.* d') P.>= (n' P.* d)
  {-# INLINEABLE (<) #-}
  Rational n d < Rational n' d' = (n P.* d') P.< (n' P.* d)
  {-# INLINEABLE (>) #-}
  Rational n d > Rational n' d' = (n P.* d') P.> (n' P.* d)

instance Haskell.Ord Rational where
  compare (Rational n d) (Rational n' d') = Haskell.compare (n Haskell.* d') (n' Haskell.* d)
  Rational n d <= Rational n' d' = (n Haskell.* d') Haskell.<= (n' Haskell.* d)
  Rational n d >= Rational n' d' = (n Haskell.* d') Haskell.>= (n' Haskell.* d)
  Rational n d < Rational n' d' = (n Haskell.* d') Haskell.< (n' Haskell.* d)
  Rational n d > Rational n' d' = (n Haskell.* d') Haskell.> (n' Haskell.* d)

instance P.AdditiveSemigroup Rational where
  {-# INLINEABLE (+) #-}
  Rational n d + Rational n' d' =
    let newNum = (n P.* d') P.+ (n' P.* d)
        newDen = d P.* d'
        gcd' = euclid newNum newDen
     in Rational
          (newNum `Builtins.quotientInteger` gcd')
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
     in Rational
          (newNum `Builtins.quotientInteger` gcd')
          (newDen `Builtins.quotientInteger` gcd')

instance P.MultiplicativeSemigroup Rational where
  {-# INLINEABLE (*) #-}
  Rational n d * Rational n' d' =
    let newNum = n P.* n'
        newDen = d P.* d'
        gcd' = euclid newNum newDen
     in Rational
          (newNum `Builtins.quotientInteger` gcd')
          (newDen `Builtins.quotientInteger` gcd')

instance P.MultiplicativeMonoid Rational where
  {-# INLINEABLE one #-}
  one = Rational P.one P.one

instance P.Module Integer Rational where
  {-# INLINEABLE scale #-}
  scale i (Rational n d) =
    let newNum = i P.* n
        gcd' = euclid newNum d
     in Rational
          (newNum `Builtins.quotientInteger` gcd')
          (d `Builtins.quotientInteger` gcd')

instance HasBlueprintDefinition Rational where
  type Unroll Rational = '[Rational, Integer]

instance
  HasSchemaDefinition Integer referencedTypes
  => HasBlueprintSchema Rational referencedTypes
  where
  schema = schema @(Integer, Integer)

instance P.ToData Rational where
  {-# INLINEABLE toBuiltinData #-}
  toBuiltinData (Rational n d) = P.toBuiltinData (n, d)

-- These instances ensure that the following invariants don't break:
--
-- 1. The denominator is greater than 0; and
-- 2. The numerator and denominator are coprime.
--
-- For invariant 1, fromBuiltinData yields Nothing on violation, while
-- unsafeFromData calls error. Invariant 2 is kept maintained by use of
-- unsafeRatio.

instance P.FromData Rational where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData dat = do
    (n, d) <- P.fromBuiltinData dat
    guard (d P./= P.zero)
    P.pure P.. unsafeRatio n P.$ d

instance P.UnsafeFromData Rational where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData = P.uncurry unsafeRatio P.. P.unsafeFromBuiltinData

-- | This mimics the behaviour of Aeson's instance for 'GHC.Rational'.
instance ToJSON Rational where
  toJSON (Rational n d) =
    object
      [ ("numerator", toJSON n)
      , ("denominator", toJSON d)
      ]

-- | This mimics the behaviour of Aeson's instance for 'GHC.Rational'.
instance FromJSON Rational where
  parseJSON = withObject "Rational" Haskell.$ \obj -> do
    n <- obj .: "numerator"
    d <- obj .: "denominator"
    case ratio n d of
      Haskell.Nothing -> Haskell.fail "Zero denominator is invalid."
      Haskell.Just r -> Haskell.pure r

{-| Makes a 'Rational' from a numerator and a denominator.

= Important note

If given a zero denominator, this function will error. If you don't mind a
size increase, and care about safety, use 'ratio' instead. -}
unsafeRatio :: Integer -> Integer -> Rational
unsafeRatio n d
  | d P.== P.zero = P.traceError P.ratioHasZeroDenominatorError
  | d P.< P.zero = unsafeRatio (P.negate n) (P.negate d)
  | P.True =
      let gcd' = euclid n d
       in Rational
            (n `Builtins.quotientInteger` gcd')
            (d `Builtins.quotientInteger` gcd')
{-# INLINEABLE unsafeRatio #-}

{-| Safely constructs a 'Rational' from a numerator and a denominator. Returns
'Nothing' if given a zero denominator. -}
ratio :: Integer -> Integer -> P.Maybe Rational
ratio n d
  | d P.== P.zero = P.Nothing
  | d P.< P.zero = P.Just (unsafeRatio (P.negate n) (P.negate d))
  | P.True =
      let gcd' = euclid n d
       in P.Just
            P.$ Rational
              (n `Builtins.quotientInteger` gcd')
              (d `Builtins.quotientInteger` gcd')
{-# INLINEABLE ratio #-}

{-| Returns the numerator of its argument.

= Note

It is /not/ true in general that @'numerator' '<$>' 'ratio' x y = x@; this
will only hold if @x@ and @y@ are coprime. This is due to 'Rational'
normalizing the numerator and denominator. -}
numerator :: Rational -> Integer
numerator (Rational n _) = n
{-# INLINEABLE numerator #-}

{-| Returns the denominator of its argument. This will always be greater than,
or equal to, 1, although the type does not describe this.

= Note

It is /not/ true in general that @'denominator' '<$>' 'ratio' x y = y@; this
will only hold if @x@ and @y@ are coprime. This is due to 'Rational'
normalizing the numerator and denominator. -}
denominator :: Rational -> Integer
denominator (Rational _ d) = d
{-# INLINEABLE denominator #-}

-- | Converts an 'Integer' into the equivalent 'Rational'.
fromInteger :: Integer -> Rational
fromInteger num = Rational num P.one
{-# INLINEABLE fromInteger #-}

{-| Produces the additive inverse of its argument.

= Note

This is specialized for 'Rational'; use this instead of the generic version
of this function, as it is significantly smaller on-chain. -}
negate :: Rational -> Rational
negate (Rational n d) = Rational (P.negate n) d
{-# INLINEABLE negate #-}

{-| Returns the absolute value of its argument.

= Note

This is specialized for 'Rational'; use this instead of the generic version
in @PlutusTx.Numeric@, as said generic version produces much larger on-chain
code than the specialized version here. -}
abs :: Rational -> Rational
abs rat@(Rational n d)
  | n P.< P.zero = Rational (P.negate n) d
  | P.True = rat
{-# INLINEABLE abs #-}

{-| @'properFraction' r@ returns the pair @(n, f)@, such that all of the
following hold:

* @'fromInteger' n 'P.+' f = r@;
* @n@ and @f@ both have the same sign as @r@; and
* @'abs' f 'P.<' 'P.one'@. -}
properFraction :: Rational -> (Integer, Rational)
properFraction (Rational n d) =
  ( n `Builtins.quotientInteger` d
  , Rational (n `Builtins.remainderInteger` d) d
  )
{-# INLINEABLE properFraction #-}

{-| Gives the reciprocal of the argument; specifically, for @r 'P./='
'P.zero'@, @r 'P.*' 'recip' r = 'P.one'@.

= Important note

The reciprocal of zero is mathematically undefined; thus, @'recip' 'P.zero'@
will error. Use with care. -}
recip :: Rational -> Rational
recip (Rational n d)
  | n P.== P.zero = P.traceError P.reciprocalOfZeroError
  | n P.< P.zero = Rational (P.negate d) (P.negate n)
  | P.True = Rational d n
{-# INLINEABLE recip #-}

{-| Returns the whole-number part of its argument, dropping any leftover
fractional part. More precisely, @'truncate' r = n@ where @(n, _) =
'properFraction' r@, but is much more efficient. -}
truncate :: Rational -> Integer
truncate (Rational n d) = n `Builtins.quotientInteger` d
{-# INLINEABLE truncate #-}

{-| @'round' r@ returns the nearest 'Integer' value to @r@. If @r@ is
equidistant between two values, the even value will be given. -}
round :: Rational -> Integer
round x =
  let (n, r) = properFraction x
      m = if r P.< P.zero then n P.- P.one else n P.+ P.one
      half = Rational 1 2
      flag = abs r P.- half
   in if
        | flag P.< P.zero -> n
        | flag P.== P.zero ->
            if Builtins.modInteger n 2 P.== P.zero
              then n
              else m
        | P.True -> m
{-# INLINEABLE round #-}

-- From GHC.Real

{-| @'gcd' x y@ is the non-negative factor of both @x@ and @y@ of which
every common factor of @x@ and @y@ is also a factor; for example
@'gcd' 4 2 = 2@, @'gcd' (-4) 6 = 2@, @'gcd' 0 4@ = @4@. @'gcd' 0 0@ = @0@. -}
gcd :: Integer -> Integer -> Integer
gcd a b = gcd' (P.abs a) (P.abs b)
  where
    gcd' a' b'
      | b' P.== P.zero = a'
      | P.True = gcd' b' (a' `Builtins.remainderInteger` b')
{-# INLINEABLE gcd #-}

-- Helpers

-- Euclid's algorithm
euclid :: Integer -> Integer -> Integer
euclid x y
  | y P.== P.zero = x
  | P.True = euclid y (x `Builtins.modInteger` y)
{-# INLINEABLE euclid #-}

instance Enum Rational where
  {-# INLINEABLE succ #-}
  succ (Rational n d) = Rational (n P.+ d) d
  {-# INLINEABLE pred #-}
  pred (Rational n d) = Rational (n P.- d) d
  {-# INLINEABLE toEnum #-}
  toEnum = fromInteger
  {-# INLINEABLE fromEnum #-}
  fromEnum = truncate
  {-# INLINEABLE enumFromTo #-}
  enumFromTo x lim
    -- See why adding half is needed in the Haskell report: https://www.haskell.org/onlinereport/haskell2010/haskellch6.html
    | x P.> lim P.+ Rational 1 2 = []
    | P.True = x : enumFromTo (succ x) lim
  {-# INLINEABLE enumFromThenTo #-}
  enumFromThenTo x y lim =
    if delta P.>= P.zero
      then up_list x
      else dn_list x
    where
      delta = y P.- x
      -- denominator of delta cannot be zero because it is constructed from two well-formed ratios. So it is safe to use unsafeRatio
      mid = numerator delta `unsafeRatio` (denominator delta P.* 2)
      up_list x1 =
        -- See why adding mid is needed in the Haskell report: https://www.haskell.org/onlinereport/haskell2010/haskellch6.html
        if x1 P.> lim P.+ mid
          then []
          else x1 : up_list (x1 P.+ delta)
      dn_list x1 =
        -- See why adding mid is needed in the Haskell report: https://www.haskell.org/onlinereport/haskell2010/haskellch6.html
        if x1 P.< lim P.+ mid
          then []
          else x1 : dn_list (x1 P.+ delta)

{-| Converts a GHC 'Ratio.Rational', preserving value.

Note: Does not work on-chain. -}
fromHaskellRatio :: HS.Rational -> Rational
fromHaskellRatio r = unsafeRatio (HS.numerator r) (HS.denominator r)

{-| Converts a 'Rational' to a GHC 'Ratio.Rational', preserving value.

Note: Does not work on-chain. -}
toHaskellRatio :: Rational -> HS.Rational
toHaskellRatio (Rational n d) = n HS.% d

{-# DEPRECATED fromGHC "Use fromHaskellRatio instead" #-}
fromGHC :: HS.Rational -> Rational
fromGHC = fromHaskellRatio
{-# DEPRECATED toGHC "Use toHaskellRatio instead" #-}
toGHC :: Rational -> HS.Rational
toGHC = toHaskellRatio

{- HLINT ignore -}

{- Note [Ratio]

An important invariant is that the denominator is always positive. This is
enforced by

\* Construction of 'Rational' numbers with 'unsafeRatio' (the constructor
  of 'Rational' is not exposed)
\* Normalizing after every numeric operation.

The 'StdLib.Spec' module has some property tests that check the behaviour of
'round', 'truncate', '>=', etc. against that of their counterparts in
'GHC.Real'.

-}

{- Note [Integer division operations]

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
\|   n  d | div mod | quot rem |
\|-----------------------------|
\|  41  5 |  8   1  |   8   1  |
\| -41  5 | -9   4  |  -8  -1  |
\|  41 -5 | -9  -4  |  -8   1  |
\| -41 -5 |  8  -1  |   8  -1  |
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
\|   n  d |  q   r |
\|-----------------|
\|  41  5 |  8   1 |
\| -41  5 | -9   4 |
\|  41 -5 | -8   1 |
\| -41 -5 |  9   4 |
-------------------

We get a positive remainder in all cases, but note for instance that the pairs
(41,5) and (-41,-5) give different results, which might be unexpected.

For a discussion of the pros and cons of various versions of integer division,
see Raymond T. Boute, "The Euclidean definition of the functions div and mod",
ACM Transactions on Programming Languages and Systems, April 1992.  (PDF at
https://core.ac.uk/download/pdf/187613369.pdf)
-}
