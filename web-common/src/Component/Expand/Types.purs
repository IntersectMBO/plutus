module Component.Expand.Types where

import Halogen as H
import Halogen.HTML as HH

type Input parentSlots parentAction m
  = { initial :: State
    , render ::
        forall a.
        { state :: State, toggle :: a, raise :: parentAction -> a } ->
        H.ComponentHTML a parentSlots m
    }

data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (State -> a)

data State
  = Opened
  | Closed

type Slot
  = H.Slot Query

type Component parentSlots parentAction m
  = H.Component HH.HTML Query (Input parentSlots parentAction m) parentAction m
