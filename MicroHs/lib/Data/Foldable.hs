-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Foldable
-- Copyright   :  Ross Paterson 2005
-- License     :  BSD-style (see the LICENSE file in the distribution)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  stable
-- Portability :  portable
--
-- Class of data structures that can be folded to a summary value.
--
-----------------------------------------------------------------------------

module Data.Foldable (
    Foldable(..),
    -- * Special biased folds
    foldrM,
    foldlM,
    -- * Folding actions
    -- ** Applicative actions
    traverse_,
    for_,
    sequenceA_,
    asum,
    -- ** Monadic actions
    mapM_,
    forM_,
    sequence_,
    msum,
    -- * Specialized folds
    concat,
    concatMap,
    and,
    or,
    any,
    all,
    maximumBy,
    minimumBy,
    -- * Searches
    notElem,
    find
    ) where
import Control.Applicative (Alternative (..), Applicative (..))
import Control.Error
import Control.Monad (Monad (..), MonadPlus (..))
import Data.Bool
import Data.Either
import Data.Eq
import Data.Foldable.Internal
import Data.Function
import Data.Functor.Const
import Data.Functor.Identity
import Data.List qualified as List
import Data.List_Type hiding (concatMap)
import Data.Maybe
import Data.Monoid
import Data.Monoid.Internal hiding (Max (..), Min (..))
import Data.Num
import Data.Ord
import Data.Proxy
import Prelude qualified ()
import Primitives

infix  4 `elem`, `notElem`

class Foldable (t :: Type -> Type) where
    {-# MINIMAL foldMap | foldr #-}

    fold :: forall m . Monoid m => t m -> m
    fold = foldMap id

    foldMap :: forall m a . Monoid m => (a -> m) -> t a -> m
    foldMap f = foldr (mappend . f) mempty

    foldMap' :: forall m a . Monoid m => (a -> m) -> t a -> m
    foldMap' f = foldl' (\ acc a -> acc <> f a) mempty

    foldr :: forall a b . (a -> b -> b) -> b -> t a -> b
    foldr f z t = appEndo (foldMap (Endo . f) t) z

    foldr' :: forall a b . (a -> b -> b) -> b -> t a -> b
    foldr' f z0 xs =
        foldl (\ k x z -> z `seq` k (f x z))
              id xs z0

    foldl :: forall a b . (b -> a -> b) -> b -> t a -> b
    foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

    foldl' :: forall a b . (b -> a -> b) -> b -> t a -> b
    foldl' f z0 xs =
        foldr (\ x k z -> z `seq` k (f z x))
              id xs z0

    foldr1 :: forall a . (a -> a -> a) -> t a -> a
    foldr1 f xs = fromMaybe (error "foldr1: empty structure")
                    (foldr mf Nothing xs)
      where
        mf x m = Just (case m of
                         Nothing -> x
                         Just y  -> f x y
                      )

    foldl1 :: forall a . (a -> a -> a) -> t a -> a
    foldl1 f xs = fromMaybe (error "foldl1: empty structure")
                    (foldl mf Nothing xs)
      where
        mf m y = Just (case m of
                         Nothing -> y
                         Just x  -> f x y
                      )

    toList :: forall a . t a -> [a]
    toList t = foldr (:) [] t

    null :: forall a . t a -> Bool
    null = foldr (\_ _ -> False) True

    length :: forall a . t a -> Int
    length = foldl' (\c _ -> c+1) 0

    elem :: forall a . Eq a => a -> t a -> Bool
    elem = any . (==)

    maximum :: forall a . Ord a => t a -> a
    maximum = fromMaybe (error "maximum: empty structure") .
       getMax . foldMap' (Max . Just)

    minimum :: forall a . Ord a => t a -> a
    minimum = fromMaybe (error "minimum: empty structure") .
       getMin . foldMap' (Min . Just)

    sum :: forall a . Num a => t a -> a
    sum = getSum . foldMap' Sum

    product :: forall a . Num a => t a -> a
    product = getProduct . foldMap' Product

instance Foldable Maybe where
    foldMap = maybe mempty

    foldr _ z Nothing  = z
    foldr f z (Just x) = f x z

    foldl _ z Nothing  = z
    foldl f z (Just x) = f z x

instance Foldable [] where
    elem    = List.elem
    foldl   = List.foldl
    foldl'  = List.foldl'
    foldl1  = List.foldl1
    foldr   = List.foldr
    --foldr'  = List.foldr'
    foldr1  = List.foldr1
    foldMap = (mconcat .) . List.map
    fold    = mconcat
    length  = List.length
    maximum = List.maximum
    minimum = List.minimum
    null    = List.null
    product = List.product
    sum     = List.sum
    toList  = id

instance Foldable (Either a) where
    foldMap _ (Left _)  = mempty
    foldMap f (Right y) = f y

    foldr _ z (Left _)  = z
    foldr f z (Right y) = f y z

    length (Left _)  = 0
    length (Right _) = 1

    null             = isLeft

instance Foldable Proxy where
  foldMap _ _ = mempty

instance Foldable Identity where
  foldMap f (Identity a) = f a

instance Foldable (Const m) where
  foldMap _ _ = mempty

{-
-- | @since 4.15
deriving instance Foldable Solo

-- | @since 4.7.0.0
instance Foldable ((,) a) where
    foldMap f (_, y) = f y

    foldr f z (_, y) = f y z
    length _  = 1
    null _ = False

-- | @since 4.8.0.0
instance Foldable (Array i) where
    foldr = foldrElems
    foldl = foldlElems
    foldl' = foldlElems'
    foldr' = foldrElems'
    foldl1 = foldl1Elems
    foldr1 = foldr1Elems
    toList = elems
    length = numElements
    null a = numElements a == 0

-- | @since 4.7.0.0
instance Foldable Proxy where
    foldMap _ _ = mempty
    {-# INLINE foldMap #-}
    fold _ = mempty
    {-# INLINE fold #-}
    foldr _ z _ = z
    {-# INLINE foldr #-}
    foldl _ z _ = z
    {-# INLINE foldl #-}
    foldl1 _ _ = error "foldl1: Proxy"
    foldr1 _ _ = error "foldr1: Proxy"
    length _   = 0
    null _     = True
    elem _ _   = False
    sum _      = 0
    product _  = 1

-- | @since 4.8.0.0
instance Foldable Dual where
    foldMap            = coerce

    elem               = (. getDual) . (==)
    foldl              = coerce
    foldl'             = coerce
    foldl1 _           = getDual
    foldr f z (Dual x) = f x z
    foldr'             = foldr
    foldr1 _           = getDual
    length _           = 1
    maximum            = getDual
    minimum            = getDual
    null _             = False
    product            = getDual
    sum                = getDual
    toList (Dual x)    = [x]

-- | @since 4.8.0.0
instance Foldable Sum where
    foldMap            = coerce

    elem               = (. getSum) . (==)
    foldl              = coerce
    foldl'             = coerce
    foldl1 _           = getSum
    foldr f z (Sum x)  = f x z
    foldr'             = foldr
    foldr1 _           = getSum
    length _           = 1
    maximum            = getSum
    minimum            = getSum
    null _             = False
    product            = getSum
    sum                = getSum
    toList (Sum x)     = [x]

-- | @since 4.8.0.0
instance Foldable Product where
    foldMap               = coerce

    elem                  = (. getProduct) . (==)
    foldl                 = coerce
    foldl'                = coerce
    foldl1 _              = getProduct
    foldr f z (Product x) = f x z
    foldr'                = foldr
    foldr1 _              = getProduct
    length _              = 1
    maximum               = getProduct
    minimum               = getProduct
    null _                = False
    product               = getProduct
    sum                   = getProduct
    toList (Product x)    = [x]

-- | @since 4.8.0.0
instance Foldable First where
    foldMap f = foldMap f . getFirst

-- | @since 4.8.0.0
instance Foldable Last where
    foldMap f = foldMap f . getLast

-- | @since 4.12.0.0
instance (Foldable f) => Foldable (Alt f) where
    foldMap f = foldMap f . getAlt

-- | @since 4.12.0.0
instance (Foldable f) => Foldable (Ap f) where
    foldMap f = foldMap f . getAp

instance Foldable (Arg a) where
  foldMap f (Arg _ a) = f a

-- Instances for GHC.Generics
-- | @since 4.9.0.0
instance Foldable U1 where
    foldMap _ _ = mempty
    {-# INLINE foldMap #-}
    fold _ = mempty
    {-# INLINE fold #-}
    foldr _ z _ = z
    {-# INLINE foldr #-}
    foldl _ z _ = z
    {-# INLINE foldl #-}
    foldl1 _ _ = error "foldl1: U1"
    foldr1 _ _ = error "foldr1: U1"
    length _   = 0
    null _     = True
    elem _ _   = False
    sum _      = 0
    product _  = 1

-- | @since 4.9.0.0
deriving instance Foldable V1

-- | @since 4.9.0.0
deriving instance Foldable Par1

-- | @since 4.9.0.0
deriving instance Foldable f => Foldable (Rec1 f)

-- | @since 4.9.0.0
deriving instance Foldable (K1 i c)

-- | @since 4.9.0.0
deriving instance Foldable f => Foldable (M1 i c f)

-- | @since 4.9.0.0
deriving instance (Foldable f, Foldable g) => Foldable (f :+: g)

-- | @since 4.9.0.0
deriving instance (Foldable f, Foldable g) => Foldable (f :*: g)

-- | @since 4.9.0.0
deriving instance (Foldable f, Foldable g) => Foldable (f :.: g)

-- | @since 4.9.0.0
deriving instance Foldable UAddr

-- | @since 4.9.0.0
deriving instance Foldable UChar

-- | @since 4.9.0.0
deriving instance Foldable UDouble

-- | @since 4.9.0.0
deriving instance Foldable UFloat

-- | @since 4.9.0.0
deriving instance Foldable UInt

-- | @since 4.9.0.0
deriving instance Foldable UWord

-- Instances for Data.Ord
-- | @since 4.12.0.0
deriving instance Foldable Down
-}

foldrM :: forall (t :: Type -> Type) (m :: Type -> Type) a b . (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl c return xs z0
  where c k x z = f x z >>= k

foldlM :: forall (t :: Type -> Type) (m :: Type -> Type) a b . (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr c return xs z0
  where c x k z = f z x >>= k

traverse_ :: forall (t :: Type -> Type) (f :: Type -> Type) a b . (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr c (pure ())
  where c x k = f x *> k
        {-# INLINE c #-}

for_ :: forall (t :: Type -> Type) (f :: Type -> Type) a b . (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
for_ = flip traverse_

mapM_ :: forall (t :: Type -> Type) (m :: Type -> Type) a b . (Foldable t, Monad m) => (a -> m b) -> t a -> m ()
mapM_ f = foldr c (return ())
  where c x k = f x >> k
        {-# INLINE c #-}

forM_ :: forall (t :: Type -> Type) (m :: Type -> Type) a b . (Foldable t, Monad m) => t a -> (a -> m b) -> m ()
forM_ = flip mapM_

sequenceA_ :: forall (t :: Type -> Type) (f :: Type -> Type) a . (Foldable t, Applicative f) => t (f a) -> f ()
sequenceA_ = foldr c (pure ())
  where c m k = m *> k
        {-# INLINE c #-}

sequence_ :: forall (t :: Type -> Type) (m :: Type -> Type) a . (Foldable t, Monad m) => t (m a) -> m ()
sequence_ = foldr c (return ())
  where c m k = m >> k
        {-# INLINE c #-}

asum :: forall (t :: Type -> Type) (f :: Type -> Type) a . (Foldable t, Alternative f) => t (f a) -> f a
asum = foldr (<|>) empty

msum :: forall (t :: Type -> Type) (m :: Type -> Type) a . (Foldable t, Alternative m, MonadPlus m) => t (m a) -> m a
msum = asum

concat :: forall (t :: Type -> Type) a . Foldable t => t [a] -> [a]
concat xs = foldr (flip (foldr (:))) [] xs

concatMap :: forall (t :: Type -> Type) a b . Foldable t => (a -> [b]) -> t a -> [b]
concatMap f xs = foldr (\x b -> foldr (:) b (f x)) [] xs

and :: forall (t :: Type -> Type) . Foldable t => t Bool -> Bool
and = getAll . foldMap All

or :: forall (t :: Type -> Type) . Foldable t => t Bool -> Bool
or = getAny . foldMap Any

any :: forall (t :: Type -> Type) a . Foldable t => (a -> Bool) -> t a -> Bool
any p = getAny . foldMap (Any . p)

all :: forall (t :: Type -> Type) a . Foldable t => (a -> Bool) -> t a -> Bool
all p = getAll . foldMap (All . p)

maximumBy :: forall (t :: Type -> Type) a . Foldable t => (a -> a -> Ordering) -> t a -> a
maximumBy cmp = fromMaybe (error "maximumBy: empty structure")
  . foldl' max' Nothing
  where
    max' mx y = Just $! case mx of
      Nothing -> y
      Just x -> case cmp x y of
        GT -> x
        _  -> y

minimumBy :: forall (t :: Type -> Type)  a . Foldable t => (a -> a -> Ordering) -> t a -> a
minimumBy cmp = fromMaybe (error "minimumBy: empty structure")
  . foldl' min' Nothing
  where
    min' mx y = Just $! case mx of
      Nothing -> y
      Just x -> case cmp x y of
        GT -> y
        _  -> x

notElem :: forall (t :: Type -> Type)  a . (Foldable t, Eq a) => a -> t a -> Bool
notElem x = not . elem x

find :: forall (t :: Type -> Type) a . Foldable t => (a -> Bool) -> t a -> Maybe a
find p = getFirst . foldMap (\ x -> First (if p x then Just x else Nothing))
