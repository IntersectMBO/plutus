{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module PlutusTx.Numeric.Class where

import           PlutusTx.Builtins.Internal
import qualified PlutusTx.Eq                as Plutus
import qualified PlutusTx.Ord               as Plutus
import           Prelude                    hiding (abs, divMod, fst, negate, snd, (*), (-), (/))

infixl 7 *
infixl 6 +, -

-- | A 'Semigroup' that it is sensible to describe using addition.
class AdditiveSemigroup a where
    (+) :: a -> a -> a

-- | A 'Monoid' that it is sensible to describe using addition and zero.
class AdditiveSemigroup a => AdditiveMonoid a where
    zero :: a

-- | A 'Group' that it is sensible to describe using addition, zero, and subtraction.
class AdditiveMonoid a => AdditiveGroup a where
    (-) :: a -> a -> a

{-# INLINABLE negate #-}
negate :: AdditiveGroup a => a -> a
negate x = zero - x

{-# INLINABLE natAbs #-}
natAbs :: (Plutus.Ord n, AdditiveGroup n) => n -> n
natAbs x = if x Plutus.< zero then negate x else x

-- | A 'Semigroup' that it is sensible to describe using multiplication.
class MultiplicativeSemigroup a where
    (*) :: a -> a -> a

-- | A 'Semigroup' that it is sensible to describe using multiplication and one.
class MultiplicativeSemigroup a => MultiplicativeMonoid a where
    one :: a

-- | A semiring.
type Semiring a = (AdditiveMonoid a, MultiplicativeMonoid a)
-- | A ring.
type Ring a = (AdditiveGroup a, MultiplicativeMonoid a)

{- | An 'AdditiveMonoid' with a notion of monus. Provides one operation @'^-'@,
 also called \'monus\'.

 = Laws

 In addition to the standard laws of being an 'AdditiveMonoid', the following
 must also hold:

 1. @a '+' (b '^-' a) = b + (a '^-' b)@
 2. @(a '^-' b) '^-' c = a '^-' (b '+' c)@
 3. @a '^-' a = 'zero'@
 4. @'zero' '^-' a = 'zero'@

 Formally-speaking, this describes a a hemigroup whose canonical order is
 total. This implies that '+' is cancellative; specifically, if @x '+' y
 = x '+' z@, then @y = z@. Additionally, for any @x@ and @y@, there must
 exist a /unique/ @z@ such that @x <= y + z@ under the canonical order.

 /See also:/

 * Gondran, Michel and Minoux, Michel; /Graphs, Dioids and Semirings: New
   Models and Algorithms/; Springer, 2008.
 * [Monus](https://en.wikipedia.org/wiki/Monus)
-}
class AdditiveMonoid a => AdditiveHemigroup a where
  (^-) :: a -> a -> a

infixl 6 ^-

{- | The combination of an 'AdditiveHemigroup' and a 'MultiplicativeMonoid' is a
 dioid; specifically, a symmetrizable dioid whose canonical order under '+' is
 total. The literature refers to this combination as a \'hemiring\', but
 formally-speaking, a hemiring doesn't necessarily possess a total canonical
 order, or indeed a monus operation.

 For symmetry with 'Ring', as well as for useful properties, we strengthen the
 notion of hemirings to \'hemiring with monus and total additive canonical
 order\', as this is the \'smallest\' useful algebra that gives us something
 we want.

 /See also:/ Gondran, Michel and Minoux, Michel; /Graphs, Dioids and
 Semirings: New Models and Algorithms/; Springer, 2008.
-}
type Hemiring a = (AdditiveHemigroup a, MultiplicativeMonoid a)

{- | The combination of an 'AdditiveHemigroup' and a 'MultiplicativeMonoid' is a
 dioid (specifically a symmetrizable dioid). We don't bother adding the
 \'symmetrizable\' to the name, as the only property of interest to us in
 \'weaker\' dioids is natural ordering, which for the types we care about, we
 already have.
 /See also:/ Gondran, Michel and Minoux, Michel; /Graphs, Dioids and
 Semirings: New Models and Algorithms/; Springer, 2008.
-}
type Dioid a = (AdditiveHemigroup a, MultiplicativeMonoid a)


{- | A semiring with a notion of (kind of) Euclidean division. This differs from
 the mathematical notion of this, as we do not exclude zero.

 Intuitively, we provide an operation corresponding to \'division with
 remainder\' which has invertibility properties in combination with /both/ '+'
 and '*'. This combination is lawful, total and closed, and is general enough
 to only require a semiring constraint; in particular, this means that both
 the ring and dioid \'universes\' can participate equally (though the presence
 of additive inverses complicates the laws somewhat).

 We avoid the paradoxes induced by defining zero division by \'coupling\'
 division and remainder, which avoids this problem, as we do not claim that
 either \'half\' of the operation is invertible by itself.

 = Laws

 In addition to the unstated laws of being a 'Semiring', the following must
 hold:

 1. If @'divMod' x y = (d, r)@ then @(d '*' y) '+' r = x@
 2. @'divMod' x 'zero' = ('zero', x)@
 3. If @'divMod' x y = (d, r)@ and @y '/=' 'zero'@, then @'zero' '<=' |r| '<'
    |y|@. This property is simplified to @'zero' '<=' r '<' y@ if there is no
    notion of additive inverses for the instance.

 = Note

 The 'Ord' constraint on the instance may or may not be a natural (or indeed,
 canonical) order.
-}
class (Plutus.Ord a, Semiring a) => EuclideanClosed a where
  -- | \'Division with remainder\', producing both results.
  divMod :: a -> a -> BuiltinPair a a

instance AdditiveSemigroup Integer where
    {-# INLINABLE (+) #-}
    (+) = addInteger

instance AdditiveMonoid Integer where
    {-# INLINABLE zero #-}
    zero = 0

instance AdditiveGroup Integer where
    {-# INLINABLE (-) #-}
    (-) = subtractInteger

instance MultiplicativeSemigroup Integer where
    {-# INLINABLE (*) #-}
    (*) = multiplyInteger

instance MultiplicativeMonoid Integer where
    {-# INLINABLE one #-}
    one = 1

instance AdditiveSemigroup Bool where
    {-# INLINABLE (+) #-}
    (+) = (||)

instance AdditiveMonoid Bool where
    {-# INLINABLE zero #-}
    zero = False

instance MultiplicativeSemigroup Bool where
    {-# INLINABLE (*) #-}
    (*) = (&&)

instance MultiplicativeMonoid Bool where
    {-# INLINABLE one #-}
    one = True

-- | 'Bool' monus \'clips\' to 'False'.
instance AdditiveHemigroup Bool where
  {-# INLINEABLE (^-) #-}
  False ^- _    = False
  True ^- False = True
  True ^- True  = False

instance EuclideanClosed Integer where
  {-# INLINEABLE divMod #-}
  divMod x y =
    if y == zero
      then BuiltinPair (zero, x)
      else BuiltinPair (quotientInteger x y, remainderInteger x y)

type Field a = (AdditiveGroup a, MultiplicativeGroup a)

type Hemifield a = (AdditiveHemigroup a, MultiplicativeGroup a)

{- | A ring with a notion of \'sign\' or \'direction\' separate from magnitude.
 This allows us to define notions of [absolute
 value](https://en.wikipedia.org/wiki/Absolute_value_(algebra)) and [signum
 function](https://en.wikipedia.org/wiki/Sign_function).

 We extend the notion of integral domain with the idea of an \'additive
 restriction\', which is a type representing \'strictly positive\' values. For
 example, the \'additive restriction\' of 'Integer' is 'Natural', and the
 \'additive restricton\' of 'Rational' is 'NatRatio'. This gives us the
 ability to move between these two types while preserving magnitude.

 = Laws

 For 'abs', the following laws apply:

 1. @'abs' x '>=' 'zero'@
 2. @'abs' 'zero' = 'zero'@
 3. @'abs' (x '*' y) = 'abs' x '*' 'abs' y@
 4. @'abs' (x '+' y) '<=' 'abs' x '+' 'abs' y@

 Additionally, if you define 'signum', the following law applies:

 5. @'abs' x '*' 'signum' x = x@

 For the methods relating to the additive restriction, the following laws
 apply:

 1. @'projectAbs' '.' 'addExtend' = 'id'@
 2. If @'abs' x = x@, then @'addExtend' '.' 'projectAbs' '$' x = x@

 Additionally, if you define 'restrictMay', the following law applies:

 3. @restrictMay x = Just y@ if and only if @abs x = x@.
-}
class (Plutus.Eq a, Ring a) => IntegralDomain a r | a -> r, r -> a where
  abs :: a -> a
  projectAbs :: a -> r
  addExtend :: r -> a
  restrictMay :: a -> Maybe r
  restrictMay x
    | abs x Plutus.== x = Just . projectAbs $ x
    | otherwise = Nothing
  signum :: a -> a
  signum x
    | x Plutus.== zero = zero
    | x Plutus.== abs x = one
    | otherwise = negate one

-- | A module, with a type of scalars which can be used to scale the values.
class (Ring s, AdditiveGroup v) => Module s v | v -> s where
    scale :: s -> v -> v

{- | A multiplicative monoid with a notion of multiplicative inverse (for
 non-zero values).

 We have to exclude division by zero, as it leads to paradoxical situations.
 This does mean that '/' and 'reciprocal' aren't total, but there's not much
 we can do about that.

 = Laws

 These assume @y /= 0@.

 1. If @x '/' y = z@ then @y '*' z = x@.
 2. @x '/' y = x '*' 'reciprocal' y@
 3. @'powInteger' x 'zero' = 'one'@
 4. @'powInteger' x 'one' = x@
 5. If @i '<' 0@, then @'powInteger' x i = 'reciprocal' '.' 'powInteger' x .
    'abs' '$' i@
 6. If @i '>' 1@, then @'powInteger' x i = 'x '*' 'powInteger' x (i '-' 'one)@
-}
class MultiplicativeMonoid a => MultiplicativeGroup a where
  {-# MINIMAL (/) | reciprocal #-}
  (/) :: a -> a -> a
  x / y = x * reciprocal y
  reciprocal :: a -> a
  reciprocal x = one / x
  powInteger :: a -> Integer -> a
  powInteger x i
    | i == zero = one
    | i == one = x
    | i < zero = reciprocal . powInteger x . natAbs $ i
    | otherwise = expBySquaring x i

infixr 8 `powInteger`

-- Helpers

{-# INLINEABLE expBySquaring #-}
-- We secretly know that 'i' is always positive.
expBySquaring
  :: forall a.
     MultiplicativeMonoid a
  => a
  -> Integer
  -> a
expBySquaring acc i
  | i == one = acc
  | even i = expBySquaring (square acc) . halve $ i
  | otherwise = (acc *) . expBySquaring (square acc) . halve $ i
  where
    square :: a -> a
    square y = y * y
    halve :: Integer -> Integer
    halve = (`divideInteger` 2)



-- | Non-operator version of '^-'.
{-# INLINE monus #-}
monus :: AdditiveHemigroup a => a -> a -> a
monus = (^-)

infixl 6 `monus`

-- | Gets only the division part of a 'divMod'.
{-# INLINE div #-}
div :: EuclideanClosed a => a -> a -> a
div x = fst . divMod x

infixl 7 `div`

-- | Gets only the remainder part of a 'divMod'.
{-# INLINE rem #-}
rem :: EuclideanClosed a => a -> a -> a
rem x = snd . divMod x

infixl 7 `rem`

-- | Operator version of 'powInteger'.
(^) :: MultiplicativeGroup a => a -> Integer -> a
(^) = powInteger

infixr 8 ^
