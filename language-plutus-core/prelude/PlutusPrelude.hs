{-# LANGUAGE DeriveFunctor #-}

module PlutusPrelude ( -- * Reëxports from base
                       (&&&)
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
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , Pretty (..)
                     , Word8
                     , Semigroup (..)
                     , Alternative (..)
                     , Exception
                     , PairT (..)
                     , Typeable
                     -- * Reëxports from "Control.Composition"
                     , (.*)
                     -- * Custom functions
                     , prettyString
                     , prettyText
                     , debugText
                     , render
                     , repeatM
                     , (?)
                     , Debug (..)
                     , hoist
                     -- Reëxports from "Data.Text.Prettyprint.Doc"
                     , (<+>)
                     , parens
                     , squotes
                     , Doc
                     , strToBs
                     , bsToStr
                     ) where

import           Control.Applicative                     (Alternative (..))
import           Control.Arrow                           ((&&&))
import           Control.Composition                     ((.*))
import           Control.DeepSeq                         (NFData)
import           Control.Exception                       (Exception, throw)
import           Control.Monad                           ((<=<))
import           Control.Monad                           (guard, join)
import           Data.Bifunctor                          (first, second)
import           Data.Bool                               (bool)
import           Data.Either                             (fromRight)
import qualified Data.ByteString.Lazy                    as BSL
import           Data.Foldable                           (fold, toList)
import           Data.Function                           (on)
import           Control.Recursion                       (Base, Corecursive, Recursive, embed, project)
import           Data.List                               (foldl')
import           Data.List.NonEmpty                      (NonEmpty (..))
import           Data.Maybe                              (isJust)
import           Data.Semigroup
import qualified Data.Text                               as T
import qualified Data.Text.Encoding                      as TE
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderStrict)
import           Data.Typeable                           (Typeable)
import           Data.Word                               (Word8)
import           GHC.Generics                            (Generic)
import           GHC.Natural                             (Natural)

infixr 2 ?

-- | This is like 'Pretty', but it dumps 'Unique's for each 'Name' / 'TyName' as
-- well.
class Debug a where
    debug :: a -> Doc ann

-- | Render a 'Program' as strict 'Text'.
prettyText :: Pretty a => a -> T.Text
prettyText = render . pretty

-- | Render a 'Program' as 'String'.
prettyString :: Pretty a => a -> String
prettyString = renderString . layoutPretty defaultLayoutOptions . pretty

debugText :: Debug a => a -> T.Text
debugText = render . debug

render :: Doc a -> T.Text
render = renderStrict . layoutSmart defaultLayoutOptions

-- | Make sure your 'Applicative' is sufficiently lazy!
repeatM :: Applicative f => f a -> f [a]
repeatM x = (:) <$> x <*> repeatM x

newtype PairT b f a = PairT
    { unPairT :: f (b, a)
    }

instance Functor f => Functor (PairT b f) where
    fmap f (PairT p) = PairT $ fmap (fmap f) p

(?) :: Alternative f => Bool -> a -> f a
(?) b x = x <$ guard b

-- | Like a version of 'everywhere' for recursion schemes. In an unreleased version thereof.
hoist :: (Recursive t, Corecursive t) => (Base t t -> Base t t) -> t -> t
hoist f = c where c = embed . f . fmap c . project

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . TE.encodeUtf8 . T.pack

bsToStr :: BSL.ByteString -> String
bsToStr = T.unpack . TE.decodeUtf8 . BSL.toStrict
