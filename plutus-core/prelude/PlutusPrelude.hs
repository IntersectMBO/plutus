{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusPrelude
  ( -- * Reexports from base
    (&)
  , (&&&)
  , (>>>)
  , (<&>)
  , toList
  , first
  , second
  , on
  , isNothing
  , isJust
  , fromMaybe
  , guard
  , foldl'
  , for_
  , traverse_
  , fold
  , for
  , throw
  , join
  , (<=<)
  , (>=>)
  , ($>)
  , fromRight
  , isRight
  , isLeft
  , void
  , through
  , coerce
  , coerceVia
  , coerceArg
  , coerceRes
  , (#.)
  , Generic
  , NFData
  , Natural
  , NonEmpty (..)
  , Word8
  , Word64
  , Alternative (..)
  , Exception
  , PairT (..)
  , Coercible
  , Typeable

    -- * Lens
  , Lens'
  , lens
  , (^.)
  , view
  , (.~)
  , set
  , (%~)
  , over
  , purely
  , (<^>)

    -- * Debugging
  , traceShowId
  , trace

    -- * Reexports from "Control.Composition"
  , (.*)

    -- * Custom functions
  , (<<$>>)
  , (<<*>>)
  , forJoin
  , foldMapM
  , reoption
  , enumerate
  , tabulateArray
  , (?)
  , ensure
  , asksM
  , timesA

    -- * Pretty-printing
  , Doc
  , ShowPretty (..)
  , Pretty (..)
  , PrettyBy (..)
  , HasPrettyDefaults
  , PrettyDefaultBy
  , PrettyAny (..)
  , Render (..)
  , display

    -- * GHCi
  , printPretty

    -- * Text
  , showText
  , Default (def)

    -- * Lists
  , zipExact
  , allSame
  , distinct
  , unsafeFromRight
  , addTheRest
  , lowerInitialChar
  ) where

import Control.Applicative
import Control.Arrow ((&&&), (>>>))
import Control.Composition ((.*))
import Control.DeepSeq (NFData)
import Control.Exception (Exception, throw)
import Control.Lens
  ( Fold
  , Identity
  , Lens'
  , ala
  , lens
  , over
  , set
  , view
  , (%~)
  , (&)
  , (.~)
  , (<&>)
  , (^.)
  )
import Control.Monad
import Control.Monad.Reader (MonadReader, ask)
import Data.Array (Array, Ix, listArray)
import Data.Bifunctor (first, second)
import Data.Char (toLower)
import Data.Coerce (Coercible, coerce)
import Data.Default.Class
import Data.Either (fromRight, isLeft, isRight)
import Data.Foldable (fold, for_, toList, traverse_)
import Data.Function (on)
import Data.Functor (($>))
#if ! MIN_VERSION_base(4,20,0)
import Data.List (foldl')
#endif
import Data.Functor.Identity (Identity (..))
import Data.List.Extra (enumerate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Semigroup (Endo (..), stimes)
import Data.Text qualified as T
import Data.Traversable (for)
import Data.Typeable (Typeable)
import Data.Word (Word64, Word8)
import Debug.Trace (trace, traceShowId)
import GHC.Generics (Generic)
import GHC.Natural (Natural)
import Prettyprinter
import Text.PrettyBy.Default
import Text.PrettyBy.Internal

infixr 2 ?
infixl 4 <<$>>, <<*>>
infixr 6 <^>

{-| A newtype wrapper around @a@ whose point is to provide a 'Show' instance
for anything that has a 'Pretty' instance. -}
newtype ShowPretty a = ShowPretty
  { unShowPretty :: a
  }
  deriving stock (Eq)

instance Pretty a => Show (ShowPretty a) where
  show = display . unShowPretty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty (Left x) = parens ("Left" <+> pretty x)
  pretty (Right y) = parens ("Right" <+> pretty y)

{-| Default pretty-printing for the __spine__ of 'Either' (elements are pretty-printed the way
@PrettyBy config@ constraints specify it). -}
instance (PrettyBy config a, PrettyBy config b) => DefaultPrettyBy config (Either a b)

-- | An instance extending the set of types supporting default pretty-printing with 'Either'.
deriving via
  PrettyCommon (Either a b)
  instance
    PrettyDefaultBy config (Either a b) => PrettyBy config (Either a b)

{-| Coerce the second argument to the result type of the first one. The motivation for this
function is that it's often more annoying to explicitly specify a target type for 'coerce' than
to construct an explicit coercion function, so this combinator can be used in cases like that.
Plus the code reads better, as it becomes clear what and where gets wrapped/unwrapped. -}
coerceVia :: Coercible a b => (a -> b) -> a -> b
coerceVia _ = coerce
{-# INLINE coerceVia #-}

-- | Same as @\f -> f . coerce@, but does not create any closures and so is completely free.
coerceArg :: Coercible a b => (a -> s) -> b -> s
coerceArg = coerce
{-# INLINE coerceArg #-}

-- | Same as @\f -> coerce . f@, but does not create any closures and so is completely free.
coerceRes :: Coercible s t => (a -> s) -> a -> t
coerceRes = coerce
{-# INLINE coerceRes #-}

-- See Note [Function coercion] in GHC.Internal.Data.Functor.Utils.
-- | Same as @(.)@, but ignores the first argument and uses a no-op coerction instead.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> a -> c
(#.) _ = coerce
{-# INLINE (#.) #-}

(<<$>>) :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
(<<$>>) = fmap . fmap

(<<*>>) :: (Applicative f1, Applicative f2) => f1 (f2 (a -> b)) -> f1 (f2 a) -> f1 (f2 b)
(<<*>>) = liftA2 (<*>)

-- | Makes an effectful function ignore its result value and return its input value.
through :: Functor f => (a -> f b) -> (a -> f a)
through f x = f x $> x

forJoin :: (Monad m, Traversable m, Applicative f) => m a -> (a -> f (m b)) -> f (m b)
forJoin a f = join <$> for a f

-- | Fold a monadic function over a 'Foldable'. The monadic version of 'foldMap'.
foldMapM :: (Foldable f, Monad m, Monoid b) => (a -> m b) -> f a -> m b
foldMapM f xs = foldr step return xs mempty
  where
    step x r z = f x >>= \y -> r $! z `mappend` y

{-| This function generalizes 'eitherToMaybe', 'eitherToList',
'listToMaybe' and other such functions. -}
reoption :: (Foldable f, Alternative g) => f a -> g a
reoption = foldr (const . pure) empty

{-| Basically a @Data.Functor.Representable@ instance for 'Array'.
We can't provide an actual instance because of the @Distributive@ superclass: @Array i@ is not
@Distributive@ unless we assume that indices in an array range over the entirety of @i@. -}
tabulateArray :: (Bounded i, Enum i, Ix i) => (i -> a) -> Array i a
tabulateArray f = listArray (minBound, maxBound) $ map f enumerate

newtype PairT b f a = PairT
  { unPairT :: f (b, a)
  }

instance Functor f => Functor (PairT b f) where
  fmap f (PairT p) = PairT $ fmap (fmap f) p

-- | @b ? x@ is equal to @pure x@ whenever @b@ holds and is 'empty' otherwise.
(?) :: Alternative f => Bool -> a -> f a
(?) b x = x <$ guard b

-- | @ensure p x@ is equal to @pure x@ whenever @p x@ holds and is 'empty' otherwise.
ensure :: Alternative f => (a -> Bool) -> a -> f a
ensure p x = p x ? x

-- | A monadic version of 'asks'.
asksM :: MonadReader r m => (r -> m a) -> m a
asksM k = ask >>= k

-- For GHCi to use this properly it needs to be in a registered package, hence
-- why we're naming such a trivial thing.
-- | A command suitable for use in GHCi as an interactive printer.
printPretty :: Pretty a => a -> IO ()
printPretty = print . pretty

showText :: Show a => a -> T.Text
showText = T.pack . show

purely :: ((a -> Identity b) -> c -> Identity d) -> (a -> b) -> c -> d
purely = coerce

-- | Compose two folds to make them run in parallel. The results are concatenated.
(<^>) :: Fold s a -> Fold s a -> Fold s a
(f1 <^> f2) g s = f1 g s *> f2 g s

{-| Zips two lists of the same length together, returning 'Nothing' if they are not
the same length. -}
zipExact :: [a] -> [b] -> Maybe [(a, b)]
zipExact [] [] = Just []
zipExact (a : as) (b : bs) = (:) (a, b) <$> zipExact as bs
zipExact _ _ = Nothing

{-| Similar to Maybe's `fromJust`. Returns the `Right` and errors out with the show instance
of the `Left`. -}
unsafeFromRight :: Show e => Either e a -> a
unsafeFromRight (Right a) = a
unsafeFromRight (Left e) = error $ show e

-- | function recursively applied N times
timesA :: Natural -> (a -> a) -> a -> a
timesA = ala Endo . stimes

{-| Pair each element of the given list with all the other elements.

>>> addTheRest "abcd"
[('a',"bcd"),('b',"acd"),('c',"abd"),('d',"abc")] -}
addTheRest :: [a] -> [(a, [a])]
addTheRest [] = []
addTheRest (x : xs) = (x, xs) : map (fmap (x :)) (addTheRest xs)

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame (x : xs) = all (x ==) xs

distinct :: Eq a => [a] -> Bool
distinct = not . allSame

lowerInitialChar :: String -> String
lowerInitialChar [] = []
lowerInitialChar (c : cs) = toLower c : cs
