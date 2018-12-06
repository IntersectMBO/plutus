-- | ECharts calls we need, but aren't (yet) provided in the current version of the PureScript libraries.
module ECharts.Extras where

import Data.Foreign (toForeign)
import ECharts.Monad (DSL, set') as E
import ECharts.Types.Phantom (I)
import Prelude (class Monad, ($))

focusNodeAdjacencyAllEdges :: forall i m. Monad m => E.DSL i m
focusNodeAdjacencyAllEdges = E.set' "focusNodeAdjacency" $ toForeign "allEdges"

orientVertical :: forall i m. Monad m => E.DSL i m
orientVertical = E.set' "orient" $ toForeign "vertical"

positionBottom ∷ ∀ i m. Monad m ⇒ E.DSL (position ∷ I|i) m
positionBottom = E.set' "position" $ toForeign "bottom"
