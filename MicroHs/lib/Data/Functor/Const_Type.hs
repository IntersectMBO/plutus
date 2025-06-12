-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Functor.Const_Type(Const(..), getConst) where
import Data.Bool
import Data.Coerce
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.Ord
import Prelude qualified ()
import Primitives
import Text.Show

type Const :: forall k . Type -> k -> Type
newtype Const a b = Const a
  deriving (Eq, Ord, Show)

getConst :: forall a b . Const a b -> a
getConst (Const a) = a
