module Modal.ViewHelpers
  ( modalHeader
  ) where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Halogen (ComponentHTML)
import Halogen.Classes (closeModal)
import Halogen.HTML (ClassName(ClassName), HTML, div, h2, img, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, src)

modalHeader ::
  forall w action.
  String ->
  Maybe action ->
  HTML w action
modalHeader title mCloseAction =
  div [ classes [ ClassName "modal-header" ] ]
    ( [ h2 [ classes [ ClassName "title" ] ] [ text title ]
      ]
        <> closeWidget
    )
  where
  closeWidget = case mCloseAction of
    Nothing -> []
    Just closeAction ->
      [ div [ class_ (ClassName "modal-close"), onClick $ const $ Just closeAction ]
          [ img [ src closeModal ] ]
      ]
