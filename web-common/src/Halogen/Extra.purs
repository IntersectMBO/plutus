module Halogen.Extra where

import Prelude
import Data.Bifunctor (bimap)
import Data.Lens (Lens', set, view)
import Halogen (ComponentHTML, get)
import Halogen.Query (HalogenM)
import Halogen.Query.HalogenM (imapState, mapAction)

mapSubmodule ::
  forall m action action' state state' slots msg.
  Functor m =>
  Lens' state state' ->
  (action' -> action) ->
  HalogenM state' action' slots msg m
    ~> HalogenM state action slots msg m
mapSubmodule lens wrapper halogen = do
  currentState <- get
  let
    setState = flip (set lens) currentState
  let
    getState = view lens
  (imapState setState getState <<< mapAction wrapper) halogen

renderSubmodule ::
  forall m action action' state state' slots.
  Lens' state state' ->
  (action' -> action) ->
  (state' -> ComponentHTML action' slots m) ->
  state ->
  ComponentHTML action slots m
renderSubmodule lens wrapper renderer state = bimap (map wrapper) wrapper (renderer (view lens state))
