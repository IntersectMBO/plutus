-- | This module contains the implementation and entry point of the component
module Component.Modal (render) where

import Prologue
import Component.Box (Preset(..), box)
import Component.Modal.Types (State(..))
import Halogen.HTML (HTML, text)

render :: forall w i a. State a -> Array String -> (Boolean -> a -> HTML w i) -> HTML w i
render state extraClasses renderChildren =
  box NoSpace classes case state of
    Initial -> text ""
    Active open a -> renderChildren open a
  where
  classes = baseClasses <> visibilityClasses <> extraClasses

  baseClasses = [ "overflow-hidden", "absolute", "inset-0" ]

  visibilityClasses = case state of
    Initial -> [ "opacity-0", "pointer-events-none" ]
    Active false _ -> [ "opacity-0", "pointer-events-none" ]
    Active true _ -> [ "opacity-1" ]
