module Component.Expand
  ( component
  , expand
  , expand_
  , toggle
  , module Types
  ) where

import Prologue
import Component.Expand.State (handleAction, handleQuery, initialState)
import Component.Expand.Types (Action(..), Component, ComponentHTML, Slot, State)
import Component.Expand.Types (Action, Component, ComponentHTML, Input, Query(..), Slot, State(..)) as Types
import Data.Symbol (SProxy(..))
import Halogen as H
import Halogen.HTML as HH

expandSlot :: SProxy "expandSlot"
expandSlot = SProxy

expand ::
  forall slots slot m parentAction parentSlots.
  Ord slot =>
  Monad m =>
  slot ->
  State ->
  (State -> ComponentHTML parentSlots parentAction m) ->
  H.ComponentHTML parentAction ( expandSlot :: Slot parentAction slot | slots ) m
expand slot initial render =
  HH.slot
    expandSlot
    slot
    component
    { initial, render }
    Just

expand_ ::
  forall slots slot m parentAction parentSlots.
  Ord slot =>
  Monad m =>
  slot ->
  State ->
  (State -> ComponentHTML parentSlots Void m) ->
  H.ComponentHTML parentAction ( expandSlot :: Slot Void slot | slots ) m
expand_ slot initial render =
  HH.slot expandSlot slot component
    { initial
    , render
    }
    $ const Nothing

component ::
  forall parentSlots parentAction m.
  Monad m =>
  Component parentSlots parentAction m
component =
  H.mkComponent
    { initialState
    , render: \{ render, state } -> render state
    , eval:
        H.mkEval
          H.defaultEval
            { handleAction = handleAction
            , handleQuery = handleQuery
            , receive = Just <<< Receive
            }
    }

toggle :: forall parentSlots parentAction m. Action parentSlots parentAction m
toggle = AToggle

raise ::
  forall parentSlots parentAction m.
  parentAction ->
  Action parentSlots parentAction m
raise = Raise
