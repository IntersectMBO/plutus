-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Either(module Data.Either) where
import Control.Applicative
import Control.Monad
import Data.Bool
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.Ord
import Prelude qualified ()
import Primitives
import Text.Show

data Either a b = Left a | Right b
  deriving (Eq, Ord)

either :: forall a b r . (a -> r) -> (b -> r) -> Either a b -> r
either f _ (Left  a) = f a
either _ f (Right b) = f b

isLeft :: forall a b . Either a b -> Bool
isLeft (Left  _) = True
isLeft (Right _) = False

isRight :: forall a b . Either a b -> Bool
isRight (Left  _) = False
isRight (Right _) = True

instance (Show a, Show b) => Show (Either a b) where
  showsPrec p (Left  a) = showParen (p>=appPrec1) (showString "Left "  . showsPrec appPrec1 a)
  showsPrec p (Right b) = showParen (p>=appPrec1) (showString "Right " . showsPrec appPrec1 b)

instance Functor (Either a) where
  fmap _ (Left a)  = Left a
  fmap f (Right b) = Right (f b)

instance Applicative (Either a) where
  pure b              = Right b
  Right f <*> Right x = Right (f x)
  Right _ <*> Left a  = Left a
  Left a  <*> _       = Left a

instance Monad (Either a) where
  Right b >>= k = k b
  Left a  >>= _ = Left a
