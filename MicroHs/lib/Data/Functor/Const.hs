-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Functor.Const(Const(..), getConst) where
import Control.Applicative
import Control.Monad
import Data.Bool
import Data.Eq
import Data.Function
import Data.Functor
import Data.Functor.Const_Type
import Data.Int
import Data.Monoid.Internal
import Data.Ord
import Prelude qualified ()
import Primitives
import Text.Show

instance forall a . Functor (Const a) where
  fmap _ (Const a) = Const a

instance forall m . Monoid m => Applicative (Const m) where
  pure _ = Const mempty
  Const a <*> Const b = Const (a `mappend` b)
