module Component.Expand.State
  ( handleAction
  , handleQuery
  , initialState
  ) where

import Prologue
import Component.Expand.Types (Action(..), Input, Query(..), State(..))
import Component.Expand.Types.Internal (DSL, InnerState)
import Halogen as H

initialState ::
  forall parentSlots parentAction m.
  Input parentSlots parentAction m ->
  InnerState parentSlots parentAction m
initialState input =
  { state: input.initial
  , render: input.render
  }

handleQuery ::
  forall parentSlots parentAction m a.
  Monad m =>
  Query a ->
  DSL parentSlots parentAction m (Maybe a)
handleQuery = case _ of
  Open a -> do
    void $ H.modify _ { state = Opened }
    pure $ Just a
  Close a -> do
    void $ H.modify _ { state = Closed }
    pure $ Just a
  Toggle a -> do
    handleAction AToggle
    pure $ Just a
  IsOpen k -> Just <<< k <$> H.gets _.state

handleAction ::
  forall parentSlots parentAction m.
  Monad m =>
  Action parentSlots parentAction m ->
  DSL parentSlots parentAction m Unit
handleAction = case _ of
  AToggle ->
    H.modify_ case _ of
      state@{ state: Opened } -> state { state = Closed }
      state -> state { state = Opened }
  Raise input -> H.raise input
  Receive { render } -> void $ H.modify _ { render = render }
