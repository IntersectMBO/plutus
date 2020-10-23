module Data.Lens.Extra (hasable, useable, peruse, toArrayOf, toSetOf) where

import Control.Category ((<<<))
import Control.Monad.State.Class (class MonadState, gets)
import Data.Array as Array
import Data.HeytingAlgebra (class HeytingAlgebra)
import Data.Lens (APrism, is, has, toListOf)
import Data.Lens.Fold (Fold, preview)
import Data.List (List)
import Data.Maybe (Maybe)
import Data.Maybe.First (First)
import Data.Monoid.Disj (Disj)
import Data.Monoid.Endo (Endo)
import Data.Ord (class Ord)
import Data.Set (Set)
import Data.Set as Set

-- | Extract a `Maybe` in the context of `MonadState`.
-- ie. `preview` on a `use`.
--
-- By happy coincidence, the English language has a word that's spelt
-- like a portmanteau of 'preview+use' and means, "to look at
-- something in a relaxed way."
peruse :: forall m s t a b. MonadState s m => Fold (First a) s t a b -> m (Maybe a)
peruse = gets <<< preview

-- | Like `peruse` but for `is`
useable :: forall m s t a b r. HeytingAlgebra r => MonadState s m => APrism s t a b -> m r
useable = gets <<< is

-- | Like `peruse` but for `has`
hasable :: forall m s t a b r. HeytingAlgebra r => MonadState s m => Fold (Disj r) s t a b -> m r
hasable = gets <<< has

-- | Analagous to `toListOf`. This is included in a forthcoming
-- release of purescript-profunctor-lenses. When we update we can delete
-- this.
toArrayOf :: forall s t a b. Fold (Endo (->) (List a)) s t a b -> s -> Array a
toArrayOf p = Array.fromFoldable <<< toListOf p

-- | Analagous to `toListOf`.
toSetOf :: forall s t a b. Ord a => Fold (Endo (->) (List a)) s t a b -> s -> Set a
toSetOf p = Set.fromFoldable <<< toListOf p
