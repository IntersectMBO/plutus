{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{- | An on-chain numeric type representing non-negative numbers only.
-}
module PlutusTx.Natural.Internal (
  -- * Types,
  Natural (..),
  Parity (..),

  -- * Functions
  parity,
  powNat,
  (^+),
  (^-)
) where

import           Control.Monad              (guard)
import           Data.Aeson                 (FromJSON (parseJSON), ToJSON)
import           PlutusTx.Builtins          (matchData, unsafeDataAsI)
import           PlutusTx.Builtins.Internal hiding (unsafeDataAsI)
import           PlutusTx.IsData            (FromData (fromBuiltinData), ToData, UnsafeFromData (unsafeFromBuiltinData))
import           PlutusTx.Lift              (makeLift)
import           PlutusTx.Numeric.Class
import           PlutusTx.Prelude
import qualified PlutusTx.Prelude           as Plutus
import qualified Prelude

-- | A non-negative number.
newtype Natural = Natural Integer
  deriving
    ( AdditiveSemigroup
    , AdditiveMonoid
    , MultiplicativeSemigroup
    , MultiplicativeMonoid
    , Eq
    , Ord
    , ToData
    , ToJSON
    , Prelude.Eq
    )
    via Integer
  deriving stock (Prelude.Show)

-- | 'Natural' monus is \'difference-or-zero\'.
instance AdditiveHemigroup Natural where
  {-# INLINEABLE (^-) #-}
  Natural n ^- Natural m
    | m > n = zero
    | otherwise = Natural (n - m)

instance EuclideanClosed Natural where
  {-# INLINEABLE divMod #-}
  divMod n@(Natural x) (Natural y)
    | y == zero = BuiltinPair (zero, n)
    | y == one = BuiltinPair (n, zero)
    | otherwise = BuiltinPair
      ( Natural . divide x $ y
      , Natural . modulo x $ y
      )

instance FromJSON Natural where
  parseJSON v = Prelude.fmap Natural $ do
    i <- parseJSON v
    guard (i >= 0)
    Prelude.pure i

instance FromData Natural where
  {-# INLINEABLE fromBuiltinData #-}
  fromBuiltinData dat =
    matchData
      dat
      (\_ -> const Nothing)
      (const Nothing)
      (const Nothing)
      go
      (const Nothing)
    where
      go :: Integer -> Maybe Natural
      go x
        | x < zero = Nothing
        | otherwise = Just . Natural $ x

instance UnsafeFromData Natural where
  {-# INLINEABLE unsafeFromBuiltinData #-}
  unsafeFromBuiltinData dat =
    let asI = unsafeDataAsI dat
     in if asI >= 0
          then Natural asI
          else Plutus.error . Plutus.trace "Cannot decode a negative value to Natural" $ ()

instance IntegralDomain Integer Natural where
  {-# INLINEABLE abs #-}
  abs = natAbs
  {-# INLINEABLE signum #-}
  signum x
    | x == zero = zero
    | x < zero = negate one
    | otherwise = one
  {-# INLINEABLE projectAbs #-}
  projectAbs = Natural . abs
  {-# INLINEABLE restrictMay #-}
  restrictMay x
    | x < zero = Nothing
    | otherwise = Just . Natural $ x
  {-# INLINEABLE addExtend #-}
  addExtend (Natural i) = i


-- This is partial all over the place, but so is Enum for most things.
instance Plutus.Enum Natural where
  {-# INLINEABLE succ #-}
  succ (Natural n) = Natural (n + 1)
  {-# INLINEABLE pred #-}
  pred (Natural n)
    | n <= 0 = Plutus.error . Plutus.trace "No predecessor to Natural 0" $ ()
    | otherwise = Natural (n - 1)
  {-# INLINEABLE toEnum #-}
  toEnum i
    | i < 0 = Plutus.error . Plutus.trace "Cannot convert a negative number to a Natural" $ ()
    | otherwise = Natural i
  {-# INLINEABLE fromEnum #-}
  fromEnum (Natural n) = n

-- | A demonstration of the parity of a number.
data Parity = Even | Odd
  deriving stock (Prelude.Eq, Prelude.Show)

-- | Determine the parity of a number.
parity :: Natural -> Parity
parity (Natural n)
  | even n = Even
  | otherwise = Odd


{- | Raise by a 'Natural' power.

 = Note

 This really /ought/ to be a method of 'MultiplicativeMonoid', but as we can't
 modify type classes provided by Plutus, this is the next best option.

 = Laws

 1. @'powNat' x 'zero' = 'one'@
 2. @'powNat' x 'one' = x@
 3. If @n '>' 'one'@, then @'powNat' x n = x '*' 'powNat' x (n '^-' 'one')@
-}
{-# INLINEABLE powNat #-}
powNat :: MultiplicativeMonoid m => m -> Natural -> m
powNat x (Natural n) =
  if n == zero
    then one
    else expBySquaring x n

infixr 8 `powNat`

-- | 'powNat' as an infix operator.
{-# INLINEABLE (^+) #-}
(^+) :: MultiplicativeMonoid m => m -> Natural -> m
(^+) = powNat

infixr 8 ^+

makeLift ''Natural
