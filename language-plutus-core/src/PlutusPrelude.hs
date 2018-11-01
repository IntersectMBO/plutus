{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusPrelude ( -- * Reëxports from base
                       (&)
                     , (&&&)
                     , toList
                     , bool
                     , first
                     , second
                     , on
                     , isJust
                     , guard
                     , foldl'
                     , fold
                     , throw
                     , join
                     , (<=<)
                     , fromRight
                     , isRight
                     , void
                     , ($>)
                     , (<$)
                     , through
                     , coerce
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
                     -- * Reëxports from "Control.Composition"
                     , (.*)
                     -- * Custom functions
                     , (<<$>>)
                     , (<<*>>)
                     , foldMapM
                     , repeatM
                     , (?)
                     , hoist
                     -- * Reëxports from "Data.Text.Prettyprint.Doc"
                     , (<+>)
                     , parens
                     , brackets
                     , hardline
                     , squotes
                     , list
                     , Doc
                     , strToBs
                     , bsToStr
                     , indent
                     -- * Pretty-printing
                     , Pretty (..)
                     , DefaultPrettyBy (..)
                     , PrettyBy (..)
                     , PrettyConfigIgnore (..)
                     , PrettyConfigAttach (..)
                     , docString
                     , docText
                     , prettyString
                     , prettyText
                     , prettyStringBy
                     , prettyTextBy
                     -- * Custom pretty-printing functions
                     , module X
                     -- * Integer arithmetic
                     , isqrt
                     , iasqrt
                     , ilogFloor
                     , ilogRound
                     ) where

import           Control.Applicative                     (Alternative (..))
import           Control.Arrow                           ((&&&))
import           Control.Composition                     ((.*))
import           Control.DeepSeq                         (NFData)
import           Control.Exception                       (Exception, throw)
import           Control.Lens
import           Control.Monad                           (guard, join, (<=<))
import           Data.Bifunctor                          (first, second)
import           Data.Bool                               (bool)
import qualified Data.ByteString.Lazy                    as BSL
import           Data.Coerce                             (Coercible, coerce)
import           Data.Either                             (fromRight, isRight)
import           Data.Foldable                           (fold, toList)
import           Data.Function                           (on)
import           Data.Functor                            (void, ($>), (<$))
import           Data.Functor.Foldable                   (Base, Corecursive, Recursive, embed, project)
import           Data.List                               (foldl')
import           Data.List.NonEmpty                      (NonEmpty (..))
import           Data.Maybe                              (isJust)
import qualified Data.Text                               as T
import qualified Data.Text.Encoding                      as TE
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Custom        as X
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderStrict)
import           Data.Typeable                           (Typeable)
import           Data.Word                               (Word8)
import           Debug.Trace
import           GHC.Generics
import           GHC.Natural                             (Natural)

import           Data.Functor.Compose

infixr 2 ?
infixl 4 <<$>>, <<*>>

-- | This class is used in order to provide default implementations of 'PrettyBy' for
-- particular @config@s. Whenever a @Config@ is a sum type of @Subconfig1@, @Subconfig2@, etc,
-- we can define a single 'DefaultPrettyBy' instance and then derive @PrettyBy Config a@ for each
-- @a@ provided the @a@ implements the @PrettyBy Subconfig1@, @PrettyBy Subconfig2@, etc instances.
--
-- Example:
--
-- > data Config = Subconfig1 Subconfig1 | Subconfig2 Subconfig2
-- >
-- > instance (PrettyBy Subconfig1 a, PrettyBy Subconfig2 a) => DefaultPrettyBy Config a where
-- >     defaultPrettyBy (Subconfig1 subconfig1) = prettyBy subconfig1
-- >     defaultPrettyBy (Subconfig2 subconfig2) = prettyBy subconfig2
--
-- Now having in scope  @PrettyBy Subconfig1 A@ and @PrettyBy Subconfig2 A@
-- and the same instances for @B@ we can write
--
-- > instance PrettyBy Config A
-- > instance PrettyBy Config B
--
-- and the instances will be derived for us.
class DefaultPrettyBy config a where
    defaultPrettyBy :: config -> a -> Doc ann

-- | Overloaded configurable conversion to 'Doc'. I.e. like 'Pretty', but parameterized by a @config@.
-- This class is interoperable with the 'Pretty' class via 'PrettyConfigIgnore' and 'PrettyConfigAttatch'.
class PrettyBy config a where
    prettyBy :: config -> a -> Doc ann
    default prettyBy :: DefaultPrettyBy config a => config -> a -> Doc ann
    prettyBy = defaultPrettyBy

-- | A newtype wrapper around @a@ which point is to provide a 'PrettyBy config' instance
-- for anything that has a 'Pretty' instance.
newtype PrettyConfigIgnore a = PrettyConfigIgnore
    { unPrettyConfigIgnore :: a
    }

-- | A config together with some value. The point is to provide a 'Pretty' instance
-- for anything that has a 'PrettyBy config' instance.
data PrettyConfigAttach config a = PrettyConfigAttach config a

instance PrettyBy config a => PrettyBy config [a] where
    prettyBy config = list . fmap (prettyBy config)

instance Pretty a => PrettyBy config (PrettyConfigIgnore a) where
    prettyBy _ (PrettyConfigIgnore x) = pretty x

instance PrettyBy config a => Pretty (PrettyConfigAttach config a) where
    pretty (PrettyConfigAttach config x) = prettyBy config x

-- | Render a 'Doc' as 'String'.
docString :: Doc a -> String
docString = renderString . layoutSmart defaultLayoutOptions

-- | Render a 'Doc' as 'Text'.
docText :: Doc a -> T.Text
docText = renderStrict . layoutSmart defaultLayoutOptions

-- | Render a value as 'String'.
prettyString :: Pretty a => a -> String
prettyString = docString . pretty

-- | Render a value as strict 'Text'.
prettyText :: Pretty a => a -> T.Text
prettyText = docText . pretty

-- | Render a value as 'String'.
prettyStringBy :: PrettyBy config a => config -> a -> String
prettyStringBy = docString .* prettyBy

-- | Render a value as strict 'Text'.
prettyTextBy :: PrettyBy config a => config -> a -> T.Text
prettyTextBy = docText .* prettyBy

(<<$>>) :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
(<<$>>) f = getCompose . fmap f . Compose

(<<*>>) :: (Applicative f1, Applicative f2) => f1 (f2 (a -> b)) -> f1 (f2 a) -> f1 (f2 b)
f <<*>> a = getCompose $ Compose f <*> Compose a

-- | Makes an effectful function ignore its result value and return its input value.
through :: Functor f => (a -> f b) -> (a -> f a)
through f x = f x $> x

-- | Fold a monadic function over a 'Foldable'. The monadic version of 'foldMap'.
foldMapM :: (Foldable f, Monad m, Monoid b) => (a -> m b) -> f a -> m b
foldMapM f xs = foldr step return xs mempty where
    step x r z = f x >>= \y -> r $! z `mappend` y

-- | Make sure your 'Applicative' is sufficiently lazy!
repeatM :: Applicative f => Int -> f a -> f [a]
repeatM 0 _ = pure []
repeatM n x = (:) <$> x <*> repeatM (n-1) x

newtype PairT b f a = PairT
    { unPairT :: f (b, a)
    }

instance Functor f => Functor (PairT b f) where
    fmap f (PairT p) = PairT $ fmap (fmap f) p

(?) :: Alternative f => Bool -> a -> f a
(?) b x = x <$ guard b

-- | Like a version of 'everywhere' for recursion schemes.
hoist :: (Recursive t, Corecursive t) => (Base t t -> Base t t) -> t -> t
hoist f = c where c = embed . f . fmap c . project

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . TE.encodeUtf8 . T.pack

bsToStr :: BSL.ByteString -> String
bsToStr = T.unpack . TE.decodeUtf8 . BSL.toStrict

-- | The integer square root.
-- Throws an 'error' on negative input.
isqrt :: Integer -> Integer
isqrt n
    | n < 0     = error "isqrt: negative number"
    | n <= 1    = n
    | otherwise = head $ dropWhile (not . isRoot) iters
    where
        sqr = (^ (2 :: Int))
        twopows = iterate sqr 2
        (lowerRoot, lowerN) = last . takeWhile ((n >=) . snd) $ zip (1 : twopows) twopows
        newtonStep x = (x + n `div` x) `div` 2
        iters = iterate newtonStep $ isqrt (n `div` lowerN) * lowerRoot
        isRoot r = sqr r <= n && n < sqr (r + 1)

-- | The integer square root that acts on negative numbers like this:
--
-- >>> iasqrt (-4)
-- -2
iasqrt :: Integer -> Integer
iasqrt n = signum n * isqrt (abs n)

-- | Compute the maximal @p@ such that @b ^ p <= x@.
ilogFloor :: Integer -> Integer -> Integer
ilogFloor b x
    | x < b     = 0
    | otherwise = go (x `div` (b ^ l)) l
    where
        l = 2 * ilogFloor (b * b) x
        go x' l' = if x' < b then l' else go (x' `div` b) (l' + 1)

-- | Compute the minimal @p@ such that @x <= b ^ p@.
ilogRound :: Integer -> Integer -> Integer
-- That's a really stupid implementation.
ilogRound b x
    | b ^ p == x = p
    | otherwise  = p + 1
    where p = ilogFloor b x
