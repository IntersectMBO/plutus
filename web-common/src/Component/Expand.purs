module Component.Expand
  ( component
  , module Component.Expand.Types
  ) where

import Prologue
import Component.Expand.Types (Component, Input, Query(..), Slot, State(..))
import Halogen as H

component :: forall ps pa m. Monad m => Component ps pa m
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

data Action ps pa m
  = Toggled
  | Raise pa
  | Receive (Input ps pa m)

type InnerState ps pa m
  = { state :: State
    , render ::
        forall a.
        { state :: State, toggle :: a, raise :: pa -> a } ->
        H.ComponentHTML a ps m
    }

type DSL ps pa m a
  = H.HalogenM (InnerState ps pa m) (Action ps pa m) ps pa m a

initialState :: forall ps pa m. Input ps pa m -> InnerState ps pa m
initialState input =
  { state: input.initial
  , render: input.render
  }

handleQuery :: forall ps pa m a. Monad m => Query a -> DSL ps pa m (Maybe a)
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

handleAction :: forall ps pa m. Monad m => Action ps pa m -> DSL ps pa m Unit
handleAction = case _ of
  Toggled ->
    H.modify_ case _ of
      state@{ state: Opened } -> state { state = Closed }
      state -> state { state = Opened }
  Raise input -> H.raise input
  Receive { render } -> void $ H.modify _ { render = render }
