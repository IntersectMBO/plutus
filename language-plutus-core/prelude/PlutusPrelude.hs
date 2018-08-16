{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
                     , freshInt
                     , dropFresh
                     , prettyText
                     , debugText
                     , render
                     , repeatM
                     , (?)
                     , Debug (..)
                     , Fresh
                     -- Reëxports from "Data.Text.Prettyprint.Doc"
                     , (<+>)
                     , parens
                     , squotes
                     , Doc
                     ) where

import           Control.Applicative                     (Alternative (..))
import           Control.Arrow                           ((&&&))
import           Control.Composition                     ((.*))
import           Control.DeepSeq                         (NFData)
import           Control.Exception                       (Exception, throw)
import           Control.Monad                           (guard, join)
import           Control.Monad.Trans.Reader
import           Data.Bifunctor                          (first, second)
import           Data.Bool                               (bool)
import           Data.Foldable                           (fold, toList)
import           Data.Function                           (on)
import           Data.List                               (foldl')
import           Data.List.NonEmpty                      (NonEmpty (..))
import           Data.Maybe                              (isJust)
import           Data.Semigroup
import           Data.Supply
import qualified Data.Text                               as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderStrict)
import           Data.Typeable                           (Typeable)
import           Data.Word                               (Word8)
import           GHC.Generics                            (Generic)
import           GHC.Natural                             (Natural)
import           System.IO.Unsafe

infixr 2 ?

-- | This is like 'Pretty', but it dumps 'Unique's for each 'Name' / 'TyName' as
-- well.
class Debug a where
    debug :: a -> Doc ann

-- | Render a 'Program' as strict 'Text'.
prettyText :: Pretty a => a -> T.Text
prettyText = render . pretty

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

newtype Fresh a = Fresh
    { unFresh :: Reader (Supply Int) a
    } deriving (Functor)

instance Applicative Fresh where
    pure                = Fresh . pure
    Fresh g <*> Fresh f = Fresh . reader $ \s ->
        let (s1, s2) = split2 s in runReader g s1 (runReader f s2)

instance Monad Fresh where
    Fresh g >>= h = Fresh . reader $ \s ->
        let (s1, s2) = split2 s in runReader (unFresh . h $ runReader g s1) s2

freshInt :: Fresh Int
freshInt = Fresh $ reader supplyValue

dropFresh :: Fresh a -> a
dropFresh (Fresh f) = runReader f $ unsafePerformIO newEnumSupply
{-# NOINLINE dropFresh #-}

(?) :: Alternative f => Bool -> a -> f a
(?) b x = x <$ guard b

prettyString :: Pretty a => a -> String
prettyString = renderString . layoutPretty defaultLayoutOptions . pretty
