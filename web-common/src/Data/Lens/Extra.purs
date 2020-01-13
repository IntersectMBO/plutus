module Data.Lens.Extra (peruse) where

import Control.Category ((<<<))
import Control.Monad.State.Class (class MonadState, gets)
import Data.Lens.Fold (Fold, preview)
import Data.Maybe (Maybe)
import Data.Maybe.First (First)

-- | Extract a `Maybe` in the context of `MonadState`.
-- ie. `preview` on a `use`.
--
-- By happy coincidence, the English language has a word that's spelt
-- like a portmanteau of 'preview+use' and means, "to look at
-- something in a relaxed way."
peruse :: forall m s t a b. MonadState s m => Fold (First a) s t a b -> m (Maybe a)
peruse = gets <<< preview
