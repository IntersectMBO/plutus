-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Functor.Identity(Identity(..)) where
import Control.Applicative
import Control.Monad
import Data.Bool
import Data.Coerce
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.Ord
import Data.Records
import Prelude qualified ()
import Primitives
import Text.Show

newtype Identity a = Identity { runIdentity :: a }
  deriving (Eq, Ord, Show)

instance Functor Identity where
  fmap f (Identity a) = Identity (f a)

instance Applicative Identity where
  pure a = Identity a
  Identity f <*> Identity a = Identity (f a)

instance Monad Identity where
  Identity a >>= f = f a
