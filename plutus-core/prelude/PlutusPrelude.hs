{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusPrelude
    ( -- * Reexports from base
      (&)
    , (&&&)
    , (<&>)
    , toList
    , bool
    , first
    , second
    , on
    , isNothing
    , isJust
    , fromMaybe
    , guard
    , foldl'
    , fold
    , for
    , throw
    , join
    , (<=<)
    , (>=>)
    , ($>)
    , fromRight
    , isRight
    , void
    , through
    , coerce
    , coerceVia
    , coerceArg
    , coerceRes
    , Generic
    , NFData
    , Natural
    , NonEmpty (..)
    , Word8
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
    -- * Debugging
    , traceShowId
    , trace
    -- * Reexports from "Control.Composition"
    , (.*)
    -- * Custom functions
    , (<<$>>)
    , (<<*>>)
    , mtraverse
    , foldMapM
    , reoption
    , enumerate
    , tabulateArray
    , (?)
    , ensure
    , asksM
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
    -- * safe zips
    , zipWithExact
    , zipWith3Exact
    ) where

import Control.Applicative (Alternative (..), liftA2)
import Control.Arrow ((&&&))
import Control.Composition ((.*))
import Control.DeepSeq (NFData)
import Control.Exception (Exception, throw)
import Control.Lens
import Control.Monad.Reader
import Data.Array
import Data.Bifunctor (first, second)
import Data.Bool (bool)
import Data.Coerce (Coercible, coerce)
import Data.Either (fromRight, isRight)
import Data.Foldable (fold, toList)
import Data.Function (on)
import Data.Functor (($>))
import Data.List (foldl')
import Data.List.Extra (enumerate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Text qualified as T
import Data.Traversable (for)
import Data.Typeable (Typeable)
import Data.Word (Word8)
import Debug.Trace
import GHC.Generics
import GHC.Natural (Natural)
import Prettyprinter
import Text.PrettyBy.Default
import Text.PrettyBy.Internal

infixr 2 ?
infixl 4 <<$>>, <<*>>

-- | A newtype wrapper around @a@ whose point is to provide a 'Show' instance
-- for anything that has a 'Pretty' instance.
newtype ShowPretty a = ShowPretty
    { unShowPretty :: a
    } deriving stock (Eq)

instance Pretty a => Show (ShowPretty a) where
    show = display . unShowPretty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    pretty (Left  x) = parens ("Left"  <+> pretty x)
    pretty (Right y) = parens ("Right" <+> pretty y)

-- | Default pretty-printing for the __spine__ of 'Either' (elements are pretty-printed the way
-- @PrettyBy config@ constraints specify it).
instance (PrettyBy config a, PrettyBy config b) => DefaultPrettyBy config (Either a b)

-- | An instance extending the set of types supporting default pretty-printing with 'Either'.
deriving via PrettyCommon (Either a b)
    instance PrettyDefaultBy config (Either a b) => PrettyBy config (Either a b)

-- | Coerce the second argument to the result type of the first one. The motivation for this
-- function is that it's often more annoying to explicitly specify a target type for 'coerce' than
-- to construct an explicit coercion function, so this combinator can be used in cases like that.
-- Plus the code reads better, as it becomes clear what and where gets wrapped/unwrapped.
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

(<<$>>) :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
(<<$>>) = fmap . fmap

(<<*>>) :: (Applicative f1, Applicative f2) => f1 (f2 (a -> b)) -> f1 (f2 a) -> f1 (f2 b)
(<<*>>) = liftA2 (<*>)

-- | Makes an effectful function ignore its result value and return its input value.
through :: Functor f => (a -> f b) -> (a -> f a)
through f x = f x $> x

mtraverse :: (Monad m, Traversable m, Applicative f) => (a -> f (m b)) -> m a -> f (m b)
mtraverse f a = join <$> traverse f a

-- | Fold a monadic function over a 'Foldable'. The monadic version of 'foldMap'.
foldMapM :: (Foldable f, Monad m, Monoid b) => (a -> m b) -> f a -> m b
foldMapM f xs = foldr step return xs mempty where
    step x r z = f x >>= \y -> r $! z `mappend` y

-- | This function generalizes 'eitherToMaybe', 'eitherToList',
-- 'listToMaybe' and other such functions.
reoption :: (Foldable f, Alternative g) => f a -> g a
reoption = foldr (const . pure) empty

-- | Basically a @Data.Functor.Representable@ instance for 'Array'.
-- We can't provide an actual instance because of the @Distributive@ superclass: @Array i@ is not
-- @Distributive@ unless we assume that indices in an array range over the entirety of @i@.
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

zipWithExact :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithExact _ [] []         = Just []
zipWithExact f (a:as) (b:bs) = (:) (f a b) <$> zipWithExact f as bs
zipWithExact _ _ _           = Nothing

zipWith3Exact :: (a -> b -> c -> d) -> [a] -> [b] -> [c]-> Maybe [d]
zipWith3Exact _ [] [] []             = Just []
zipWith3Exact f (a:as) (b:bs) (c:cs) = (:) (f a b c) <$> zipWith3Exact f as bs cs
zipWith3Exact _ _ _ _                = Nothing
