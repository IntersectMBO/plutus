{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Evaluation.Machine.GenericSemigroup where

import           Data.Monoid            (Monoid (..))
import           Data.Semigroup         (Semigroup (..))
import           GHC.Generics
-- TODO when this import conflicts, delete this file.
import           Data.Semigroup.Generic

newtype GenericSemigroupMonoid a =
  GenericSemigroupMonoid { getGenericSemigroupMonoid :: a }

instance (Generic a, GSemigroup (Rep a)) => Semigroup (GenericSemigroupMonoid a) where
  GenericSemigroupMonoid x <> GenericSemigroupMonoid y =
    GenericSemigroupMonoid (gmappend x y)
instance (Generic a, GMonoid (Rep a)) => Monoid (GenericSemigroupMonoid a) where
  mempty = GenericSemigroupMonoid gmempty
  mappend = (<>)
