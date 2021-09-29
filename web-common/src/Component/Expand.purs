module Component.Expand
  ( component
  , module Component.Expand.Types
  ) where

import Prologue
import Component.Expand.Types (Component, Input, Query(..), Slot, State(..))
import Halogen as H

component ::
  forall parentSlots parentAction m.
  Monad m =>
  Component parentSlots parentAction m
component =
  H.mkComponent
    { initialState
    , render: \state -> state.render { raise: Raise, toggle: Toggled, state: state.state }
    , eval:
        H.mkEval
          H.defaultEval
            { handleAction = handleAction
            , handleQuery = handleQuery
            , receive = Just <<< Receive
            }
    }

data Action parentSlots parentAction m
  = Toggled
  | Raise parentAction
  | Receive (Input parentSlots parentAction m)

type InnerState parentSlots parentAction m
  = { state :: State
    , render ::
        forall a.
        { state :: State, toggle :: a, raise :: parentAction -> a } ->
        H.ComponentHTML a parentSlots m
    }

type DSL parentSlots parentAction m a
  = H.HalogenM (InnerState parentSlots parentAction m)
      ( Action parentSlots
          parentAction
          m
      )
      parentSlots
      parentAction
      m
      a

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
    handleAction Toggled
    pure $ Just a
  IsOpen k -> Just <<< k <$> H.gets _.state

handleAction ::
  forall parentSlots parentAction m.
  Monad m =>
  Action parentSlots parentAction m ->
  DSL parentSlots parentAction m Unit
handleAction = case _ of
  Toggled ->
    H.modify_ case _ of
      state@{ state: Opened } -> state { state = Closed }
      state -> state { state = Opened }
  Raise input -> H.raise input
  Receive { render } -> void $ H.modify _ { render = render }
