{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Language.PlutusTx.Foldable
  ( Foldable(..)
  , fold
  , foldr
  , foldl
  , toList
  , null
  , length
  , elem
  , sum
  , product
  , foldrM
  , foldlM
  , traverse_
  , for_
  , sequenceA_
  , asum
  , concat
  , concatMap
  , and
  , or
  , any
  , all
  , notElem
  , find
  ) where

import           Control.Applicative           (Alternative (..), Const (..))
import           Data.Coerce                   (Coercible, coerce)
import           Data.Functor.Identity         (Identity (..))
import           Data.Monoid                   (First (..))
import           Data.Semigroup                (Dual (..), Endo (..), Product (..), Sum (..))
import           GHC.Exts                      (build)
import           Language.PlutusTx.Applicative (Applicative (pure), (*>))
import           Language.PlutusTx.Bool        (not)
import           Language.PlutusTx.Eq          (Eq (..))
import           Language.PlutusTx.Functor     (id)
import           Language.PlutusTx.Monoid      (Monoid (..))
import           Language.PlutusTx.Numeric     (AdditiveMonoid, AdditiveSemigroup ((+)), MultiplicativeMonoid)
import           Language.PlutusTx.Semigroup   ((<>))
import           Prelude                       (Bool (..), Either (..), Integer, Maybe (..), Monad (..), flip, (.))

-- | Data structures that can be folded.
--
-- For example, given a data type
--
-- > data Tree a = Empty | Leaf a | Node (Tree a) a (Tree a)
--
-- a suitable instance would be
--
-- > instance Foldable Tree where
-- >    foldMap f Empty = mempty
-- >    foldMap f (Leaf x) = f x
-- >    foldMap f (Node l k r) = foldMap f l `mappend` f k `mappend` foldMap f r
--
-- This is suitable even for abstract types, as the monoid is assumed
-- to satisfy the monoid laws.  Alternatively, one could define @foldr@:
--
-- @sum@, @product@, @maximum@, and @minimum@ should all be essentially
-- equivalent to @foldMap@ forms, such as
--
-- > sum = getSum . foldMap Sum
--
-- but may be less defined.
--
-- If the type is also a 'Functor' instance, it should satisfy
--
-- > foldMap f = fold . fmap f
--
-- which implies that
--
-- > foldMap f . fmap g = foldMap (f . g)
class Foldable t where
    -- | Map each element of the structure to a monoid,
    -- and combine the results.
    foldMap :: Monoid m => (a -> m) -> t a -> m

    -- All the other methods are deliberately omitted,
    -- to make this a one-method class which has a simpler representation

instance Foldable [] where
    {-# INLINABLE foldMap #-}
    foldMap _ []     = mempty
    foldMap f (x:xs) = f x <> foldMap f xs

instance Foldable Maybe where
    {-# INLINABLE foldMap #-}
    foldMap _ Nothing  = mempty
    foldMap f (Just a) = f a

instance Foldable (Either c) where
    {-# INLINABLE foldMap #-}
    foldMap _ (Left _)  = mempty
    foldMap f (Right a) = f a

instance Foldable ((,) c) where
    {-# INLINABLE foldMap #-}
    foldMap f (_, a) = f a

instance Foldable Identity where
    {-# INLINABLE foldMap #-}
    foldMap f (Identity a) = f a

instance Foldable (Const c) where
    {-# INLINABLE foldMap #-}
    foldMap _ _ = mempty

-- | Combine the elements of a structure using a monoid.
{-# INLINABLE fold #-}
fold :: (Foldable t, Monoid m) => t m -> m
fold = foldMap id

-- | Right-associative fold of a structure.
--
-- In the case of lists, 'foldr', when applied to a binary operator, a
-- starting value (typically the right-identity of the operator), and a
-- list, reduces the list using the binary operator, from right to left:
--
-- > foldr f z [x1, x2, ..., xn] == x1 `f` (x2 `f` ... (xn `f` z)...)
--
-- Note that, since the head of the resulting expression is produced by
-- an application of the operator to the first element of the list,
-- 'foldr' can produce a terminating expression from an infinite list.
--
-- For a general 'Foldable' structure this should be semantically identical
-- to,
--
-- @foldr f z = 'List.foldr' f z . 'toList'@
--
{-# INLINABLE foldr #-}
foldr :: Foldable t => (a -> b -> b) -> b -> t a -> b
foldr f z t = appEndo (foldMap (Endo #. f) t) z

-- | Left-associative fold of a structure.
--
-- In the case of lists, 'foldl', when applied to a binary
-- operator, a starting value (typically the left-identity of the operator),
-- and a list, reduces the list using the binary operator, from left to
-- right:
--
-- > foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
--
-- Note that to produce the outermost application of the operator the
-- entire input list must be traversed. This means that 'foldl'' will
-- diverge if given an infinite list.
--
-- Also note that if you want an efficient left-fold, you probably want to
-- use 'foldl'' instead of 'foldl'. The reason for this is that latter does
-- not force the "inner" results (e.g. @z \`f\` x1@ in the above example)
-- before applying them to the operator (e.g. to @(\`f\` x2)@). This results
-- in a thunk chain \(\mathcal{O}(n)\) elements long, which then must be
-- evaluated from the outside-in.
--
-- For a general 'Foldable' structure this should be semantically identical
-- to,
--
-- @foldl f z = 'List.foldl' f z . 'toList'@
--
{-# INLINABLE foldl #-}
foldl :: Foldable t => (b -> a -> b) -> b -> t a -> b
foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

-- | List of elements of a structure, from left to right.
toList :: Foldable t => t a -> [a]
{-# INLINE toList #-}
toList t = build (\ c n -> foldr c n t)

-- | Test whether the structure is empty. The default implementation is
-- optimized for structures that are similar to cons-lists, because there
-- is no general way to do better.
{-# INLINABLE null #-}
null :: Foldable t => t a -> Bool
null = foldr (\_ _ -> False) True

-- | Returns the size/length of a finite structure as an 'Int'.  The
-- default implementation is optimized for structures that are similar to
-- cons-lists, because there is no general way to do better.
{-# INLINABLE length #-}
length :: Foldable t => t a -> Integer
length = foldl (\c _ -> c + 1) 0

-- | Does the element occur in the structure?
{-# INLINABLE elem #-}
elem :: (Foldable t, Eq a) => a -> t a -> Bool
elem = any . (==)

-- | The 'sum' function computes the sum of the numbers of a structure.
{-# INLINEABLE sum #-}
sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = getSum #. foldMap Sum

-- | The 'product' function computes the product of the numbers of a
-- structure.
{-# INLINABLE product #-}
product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = getProduct #. foldMap Product



-- | Monadic fold over the elements of a structure,
-- associating to the right, i.e. from right to left.
foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
foldrM f z0 xs = foldl c return xs z0
  where c k x z = f x z >>= k
        {-# INLINE c #-}

-- | Monadic fold over the elements of a structure,
-- associating to the left, i.e. from left to right.
foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b
foldlM f z0 xs = foldr c return xs z0
  where c x k z = f z x >>= k
        {-# INLINE c #-}

-- | Map each element of a structure to an action, evaluate these
-- actions from left to right, and ignore the results. For a version
-- that doesn't ignore the results see 'Language.PlutusTx.traverse'.
traverse_ :: (Foldable t, Applicative f) => (a -> f b) -> t a -> f ()
traverse_ f = foldr c (pure ())
  where c x k = f x *> k
        {-# INLINE c #-}

-- | 'for_' is 'traverse_' with its arguments flipped. For a version
-- that doesn't ignore the results see 'Language.PlutusTx.for'.
--
-- >>> for_ [1..4] print
-- 1
-- 2
-- 3
-- 4
for_ :: (Foldable t, Applicative f) => t a -> (a -> f b) -> f ()
{-# INLINE for_ #-}
for_ = flip traverse_

-- | Evaluate each action in the structure from left to right, and
-- ignore the results. For a version that doesn't ignore the results
-- see 'Language.PlutusTx.sequenceA'.
sequenceA_ :: (Foldable t, Applicative f) => t (f a) -> f ()
sequenceA_ = foldr c (pure ())
  where c m k = m *> k
        {-# INLINE c #-}

-- | The sum of a collection of actions, generalizing 'concat'.
--
-- >>> asum [Just "Hello", Nothing, Just "World"]
-- Just "Hello"
asum :: (Foldable t, Alternative f) => t (f a) -> f a
{-# INLINE asum #-}
asum = foldr (<|>) empty

-- | The concatenation of all the elements of a container of lists.
concat :: Foldable t => t [a] -> [a]
concat xs = build (\c n -> foldr (\x y -> foldr c y x) n xs)
{-# INLINE concat #-}

-- | Map a function over all the elements of a container and concatenate
-- the resulting lists.
concatMap :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap f xs = build (\c n -> foldr (\x b -> foldr c b (f x)) n xs)
{-# INLINE concatMap #-}

-- These use foldr rather than foldMap to avoid repeated concatenation.

-- | 'and' returns the conjunction of a container of Bools.  For the
-- result to be 'True', the container must be finite; 'False', however,
-- results from a 'False' value finitely far from the left end.
{-# INLINABLE and #-}
and :: Foldable t => t Bool -> Bool
and = product

-- | 'or' returns the disjunction of a container of Bools.  For the
-- result to be 'False', the container must be finite; 'True', however,
-- results from a 'True' value finitely far from the left end.
{-# INLINABLE or #-}
or :: Foldable t => t Bool -> Bool
or = sum

-- | Determines whether any element of the structure satisfies the predicate.
{-# INLINABLE any #-}
any :: Foldable t => (a -> Bool) -> t a -> Bool
any p = getSum #. foldMap (Sum #. p)

-- | Determines whether all elements of the structure satisfy the predicate.
{-# INLINABLE all #-}
all :: Foldable t => (a -> Bool) -> t a -> Bool
all p = getProduct #. foldMap (Product #. p)

-- | 'notElem' is the negation of 'elem'.
{-# INLINABLE notElem #-}
notElem :: (Foldable t, Eq a) => a -> t a -> Bool
notElem x = not . elem x

-- | The 'find' function takes a predicate and a structure and returns
-- the leftmost element of the structure matching the predicate, or
-- 'Nothing' if there is no such element.
{-# INLINABLE find #-}
find :: Foldable t => (a -> Bool) -> t a -> Maybe a
find p = getFirst . foldMap (\ x -> First (if p x then Just x else Nothing))

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce
{-# INLINE (#.) #-}
