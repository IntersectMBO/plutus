-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Compose
-- Copyright   :  (c) Ross Paterson 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  stable
-- Portability :  portable
--
-- Composition of functors.
--
-- @since 4.9.0.0
-----------------------------------------------------------------------------

module Data.Functor.Compose (
    Compose(..),
  ) where
import Control.Applicative
import Prelude hiding (elem, foldl, foldr, length, maximum, minimum, null, product, sum)
--import Data.Coerce (coerce)
import Data.Data (Data)
import Data.Foldable (Foldable (..))
import Data.Functor.Classes
import Data.Monoid.Internal
import Data.Traversable
--import Data.Type.Equality (TestEquality(..), (:~:)(..))
--import GHC.Generics (Generic, Generic1)
import Text.Read.Internal (Read (..), ReadPrec, readListDefault, readListPrecDefault)

infixr 9 `Compose`

newtype Compose f g a = Compose { getCompose :: f (g a) }
{-
  deriving ( Data     -- ^ @since 4.9.0.0
           , Generic  -- ^ @since 4.9.0.0
           , Generic1 -- ^ @since 4.9.0.0
           , Semigroup -- ^ @since 4.16.0.0
           , Monoid    -- ^ @since 4.16.0.0
           )

deriving instance Eq (f (g a)) => Eq (Compose f g a)
deriving instance Ord (f (g a)) => Ord (Compose f g a)

instance Read (f (g a)) => Read (Compose f g a) where
    readPrec = liftReadPrecCompose readPrec

    readListPrec = readListPrecDefault
    readList     = readListDefault
-}
instance Eq (f (g a)) => Eq (Compose f g a) where
  Compose x == Compose y  =  x == y

instance Ord (f (g a)) => Ord (Compose f g a) where
  Compose x `compare` Compose y  =  x `compare` y

instance Show (f (g a)) => Show (Compose f g a) where
    showsPrec = liftShowsPrecCompose showsPrec

instance (Eq1 f, Eq1 g) => Eq1 (Compose f g) where
    liftEq eq (Compose x) (Compose y) = liftEq (liftEq eq) x y

instance (Ord1 f, Ord1 g) => Ord1 (Compose f g) where
    liftCompare comp (Compose x) (Compose y) =
        liftCompare (liftCompare comp) x y

{-
instance (Read1 f, Read1 g) => Read1 (Compose f g) where
    liftReadPrec rp rl =
        liftReadPrecCompose (liftReadPrec rp' rl')
      where
        rp' = liftReadPrec     rp rl
        rl' = liftReadListPrec rp rl

    liftReadListPrec = liftReadListPrecDefault
    liftReadList     = liftReadListDefault
-}

instance (Show1 f, Show1 g) => Show1 (Compose f g) where
    liftShowsPrec sp sl =
        liftShowsPrecCompose (liftShowsPrec sp' sl')
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

{-
-- The workhorse for Compose's Read and Read1 instances.
liftReadPrecCompose :: ReadPrec (f (g a)) -> ReadPrec (Compose f g a)
liftReadPrecCompose rp = readData $ readUnaryWith rp "Compose" Compose
-}

-- The workhorse for Compose's Show and Show1 instances.
liftShowsPrecCompose :: (Int -> f (g a) -> ShowS) -> Int -> Compose f g a -> ShowS
liftShowsPrecCompose sp d (Compose x) = showsUnaryWith sp "Compose" d x

instance (Functor f, Functor g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (fmap (fmap f) x)
    a <$ (Compose x) = Compose (fmap (a <$) x)

instance (Foldable f, Foldable g) => Foldable (Compose f g) where
    fold (Compose t) = foldMap fold t
    foldMap f (Compose t) = foldMap (foldMap f) t
    foldMap' f (Compose t) = foldMap' (foldMap' f) t
    foldr f b (Compose fga) = foldr (\ga acc -> foldr f acc ga) b fga
    foldr' f b (Compose fga) = foldr' (\ga acc -> foldr' f acc ga) b fga
    foldl f b (Compose fga) = foldl (\acc ga -> foldl f acc ga) b fga
    foldl' f b (Compose fga) = foldl' (\acc ga -> foldl' f acc ga) b fga

    null (Compose t) = null t || getAll (foldMap (All . null) t)
    length (Compose t) = getSum (foldMap' (Sum . length) t)
    elem x (Compose t) = getAny (foldMap (Any . elem x) t)

    minimum (Compose fga) = minimum $ map minimum $ filter (not . null) $ toList fga
    maximum (Compose fga) = maximum $ map maximum $ filter (not . null) $ toList fga

    sum (Compose t) = getSum (foldMap' (Sum . sum) t)
    product (Compose t) = getProduct (foldMap' (Product . product) t)

instance (Traversable f, Traversable g) => Traversable (Compose f g) where
    traverse f (Compose t) = Compose <$> traverse (traverse f) t

instance (Applicative f, Applicative g) => Applicative (Compose f g) where
    pure x = Compose (pure (pure x))
    Compose f <*> Compose x = Compose (liftA2 (<*>) f x)
    liftA2 f (Compose x) (Compose y) =
      Compose (liftA2 (liftA2 f) x y)

-- | @since 4.9.0.0
instance (Alternative f, Applicative g) => Alternative (Compose f g) where
    empty = Compose empty
    Compose x <|> Compose y = Compose (x <|> y)

{-
-- | The deduction (via generativity) that if @g x :~: g y@ then @x :~: y@.
--
-- @since 4.14.0.0
instance (TestEquality f) => TestEquality (Compose f g) where
  testEquality (Compose x) (Compose y) =
    case testEquality x y of -- :: Maybe (g x :~: g y)
      Just Refl -> Just Refl -- :: Maybe (x :~: y)
      Nothing   -> Nothing

-- | @since 4.19.0.0
deriving instance Enum (f (g a)) => Enum (Compose f g a)
-- | @since 4.19.0.0
deriving instance Bounded (f (g a)) => Bounded (Compose f g a)
-- | @since 4.19.0.0
deriving instance Num (f (g a)) => Num (Compose f g a)
-- | @since 4.19.0.0
deriving instance Real (f (g a)) => Real (Compose f g a)
-- | @since 4.19.0.0
deriving instance Integral (f (g a)) => Integral (Compose f g a)
-- | @since 4.20.0.0
deriving instance Fractional (f (g a)) => Fractional (Compose f g a)
-- | @since 4.20.0.0
deriving instance RealFrac (f (g a)) => RealFrac (Compose f g a)
-- | @since 4.20.0.0
deriving instance Floating (f (g a)) => Floating (Compose f g a)
-- | @since 4.20.0.0
deriving instance RealFloat (f (g a)) => RealFloat (Compose f g a)
-}
