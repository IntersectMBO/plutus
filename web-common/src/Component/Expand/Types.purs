module Component.Expand.Types where

import Halogen as H
import Halogen.HTML as HH

data Action parentSlots parentAction m
  = AToggle
  | Raise parentAction
  | Receive (Input parentSlots parentAction m)

type Input parentSlots parentAction m
  = { initial :: State
    , render :: State -> ComponentHTML parentSlots parentAction m
    }

type ComponentHTML parentSlots parentAction m
  = H.ComponentHTML (Action parentSlots parentAction m) parentSlots m

data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (State -> a)

data State
  = Opened
  | Closed

type Slot parentAction slot
  = H.Slot Query parentAction slot

type Component parentSlots parentAction m
  = H.Component HH.HTML Query (Input parentSlots parentAction m) parentAction m
