-- | This module contains the implementation and entry point of the component
module Component.Modal (render) where

import Prologue
import Component.Box (Preset(..), box)
import Component.Modal.Types (State(..))
import Halogen.HTML (HTML, text)

render :: forall w i a. State a -> Array String -> (a -> Boolean -> HTML w i) -> HTML w i
render state extraClasses renderChildren =
  box NoSpace classes case state of
    Initial -> text ""
    Active a open -> renderChildren a open
  where
  classes = baseClasses <> visibilityClasses <> extraClasses

  baseClasses = [ "overflow-hidden", "absolute", "inset-0" ]

  visibilityClasses = case state of
    Initial -> [ "opacity-0", "pointer-events-none" ]
    Active _ false -> [ "opacity-0", "pointer-events-none" ]
    Active _ true -> [ "opacity-1" ]
