module Demos.Types where

import Prelude
import Analytics (class IsEvent)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Projects.Types (Lang)

newtype Demo
  = Demo String

derive instance newtypeDemo :: Newtype Demo _

data Action
  = LoadDemo Lang Demo

instance isEventAction :: IsEvent Action where
  toEvent (LoadDemo lang _) = Just { category: Just "Demos", action: "LoadDemo", label: Just (show lang), value: Nothing }
