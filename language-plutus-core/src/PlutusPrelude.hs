{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module PlutusPrelude ( (&&&)
                     , toList
                     , bool
                     , first
                     , second
                     , on
                     , guard
                     , fold
                     , throw
                     , (.*)
                     , freshInt
                     , dropFresh
                     , prettyText
                     , prettyString
                     , (?)
                     , Alternative (..)
                     , Exception
                     , Fresh
                     , Generic
                     , NFData
                     , Natural
                     , NonEmpty (..)
                     , PairT (..)
                     , Pretty (..)
                     , Typeable
                     , Word8
                     , Semigroup (..)
                     , module X
                     ) where

import           Control.Applicative       (Alternative (..))
import           Control.Arrow             (first, second, (&&&))
import           Control.Composition       ((.*))
import           Control.DeepSeq           (NFData)
import           Control.Exception         (Exception, throw)
import           Control.Monad             (guard)
import           Data.Bool                 (bool)
import           Data.Foldable             (fold, toList)
import           Data.Function             (on)
import           Data.List.NonEmpty        (NonEmpty (..))
import           Data.Semigroup
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc
import           Data.Typeable             (Typeable)
import           Data.Word                 (Word8)
import           Debug.Trace               as X
import           GHC.Generics              (Generic)
import           GHC.Natural               (Natural)

import           Control.Monad.Trans.Reader
import           Data.Supply
import           Data.Text.Prettyprint.Doc.Render.Text   (renderStrict)
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           System.IO.Unsafe

infixr 2 ?

newtype PairT b f a = PairT
    { unPairT :: f (b, a)
    }

instance Functor f => Functor (PairT b f) where
    fmap f (PairT p) = PairT $ fmap (fmap f) p
    {-# INLINE fmap #-}

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

prettyText :: Pretty a => a -> Text
prettyText = renderStrict . layoutPretty defaultLayoutOptions . pretty

prettyString :: Pretty a => a -> String
prettyString = renderString . layoutPretty defaultLayoutOptions . pretty
