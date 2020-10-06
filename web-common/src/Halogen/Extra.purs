module Halogen.Extra where

import Prelude

import Data.Lens (Lens', set, view)
import Halogen (get)
import Halogen.Query (HalogenM)
import Halogen.Query.HalogenM (imapState, mapAction)

mapSubmodule ::
  forall m action action' state state' slots msg.
  Functor m =>
  Lens' state state' ->
  (action' -> action) ->
  HalogenM state' action' slots msg m ~>
  HalogenM state action slots msg m
mapSubmodule lens wrapper halogen = do
  currentState <- get
  let
    setState = flip (set lens) currentState
  let
    getState = view lens
  (imapState setState getState <<< mapAction wrapper) halogen
