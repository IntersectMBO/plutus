module Contact.View (renderContacts) where

import Prelude hiding (div)
import Css (classNames)
import Halogen.HTML (HTML, div, text)
import MainFrame.Types (Action, State)

renderContacts :: forall p. State -> HTML p Action
renderContacts state =
  div
    [ classNames [ "p-1" ] ]
    [ text "contacts" ]
