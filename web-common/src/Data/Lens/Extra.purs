module Data.Lens.Extra (peruse, toArrayOf) where

import Control.Category ((<<<))
import Control.Monad.State.Class (class MonadState, gets)
import Data.Array as Array
import Data.Lens (toListOf)
import Data.Lens.Fold (Fold, preview)
import Data.List (List)
import Data.Maybe (Maybe)
import Data.Maybe.First (First)
import Data.Monoid.Endo (Endo)

-- | Extract a `Maybe` in the context of `MonadState`.
-- ie. `preview` on a `use`.
--
-- By happy coincidence, the English language has a word that's spelt
-- like a portmanteau of 'preview+use' and means, "to look at
-- something in a relaxed way."
peruse :: forall m s t a b. MonadState s m => Fold (First a) s t a b -> m (Maybe a)
peruse = gets <<< preview

-- | Analagous to `toListOf`. This is included in a forthcoming
-- release of purescript-profunctor-lenses. When we update we can delete
-- this.
toArrayOf :: forall s t a b. Fold (Endo (->) (List a)) s t a b -> s -> Array a
toArrayOf p = Array.fromFoldable <<< toListOf p
