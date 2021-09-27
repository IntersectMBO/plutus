module Component.Expand.Types where

import Halogen as H
import Halogen.HTML as HH

type Input ps pa m
  = { initial :: State
    , render ::
        forall a.
        { state :: State, toggle :: a, raise :: pa -> a } ->
        H.ComponentHTML a ps m
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

type Component ps pa m
  = H.Component HH.HTML Query (Input ps pa m) pa m
