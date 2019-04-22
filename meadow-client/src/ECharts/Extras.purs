-- | ECharts calls we need, but aren't (yet) provided in the current version of the PureScript libraries.
module ECharts.Extras where

import Data.Foreign
  ( toForeign
  )
import ECharts.Monad
  ( DSL
  , set'
  )
import ECharts.Types.Phantom
  ( I
  )
import Prelude
  ( class Monad
  , ($)
  )

focusNodeAdjacencyAllEdges ::
  forall i m.
  Monad m =>
  DSL i m
focusNodeAdjacencyAllEdges = set' "focusNodeAdjacency" $ toForeign "allEdges"

orientVertical ::
  forall i m.
  Monad m =>
  DSL i m
orientVertical = set' "orient" $ toForeign "vertical"

positionBottom ::
  forall i m.
  Monad m =>
  DSL (position :: I | i) m
positionBottom = set' "position" $ toForeign "bottom"
