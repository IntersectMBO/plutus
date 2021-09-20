module MainFrame.Types
  ( State
  , ChildSlots
  , Action(..)
  ) where

import Prologue
import Analytics (class IsEvent, defaultEvent)

type State
  = { placeholder :: String
    }

------------------------------------------------------------
type ChildSlots
  = (
    )

------------------------------------------------------------
data Action
  = Init

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
