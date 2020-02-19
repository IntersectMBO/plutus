{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Evaluation.Machine.GenericSemigroup (GenericSemigroupMonoid(..)) where

-- TODO when we need to support semigroup >=0.19 only, delete this file
-- and use Data.Semigroup.Generic.

#if MIN_VERSION_semigroups(0, 19, 0)

import           Data.Semigroup.Generic (GenericSemigroupMonoid(..))

#else

import           Data.Monoid            (Monoid (..))
import           Data.Semigroup         (Semigroup (..))
import           GHC.Generics
import           Data.Semigroup.Generic

newtype GenericSemigroupMonoid a =
  GenericSemigroupMonoid { getGenericSemigroupMonoid :: a }

instance (Generic a, GSemigroup (Rep a)) => Semigroup (GenericSemigroupMonoid a) where
  GenericSemigroupMonoid x <> GenericSemigroupMonoid y =
    GenericSemigroupMonoid (gmappend x y)
instance (Generic a, GMonoid (Rep a)) => Monoid (GenericSemigroupMonoid a) where
  mempty = GenericSemigroupMonoid gmempty
  mappend = (<>)

#endif
