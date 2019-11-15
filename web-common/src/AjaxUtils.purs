module AjaxUtils (ajaxErrorPane, renderForeignErrors) where

import Prelude hiding (div)
import Bootstrap (alertDanger_)
import Data.Foldable (intercalate)
import Foreign (MultipleErrors, renderForeignError)
import Halogen.HTML (ClassName(..), HTML, br_, div, text)
import Halogen.HTML.Properties (class_)
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), runAjaxError)

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div
    [ class_ $ ClassName "ajax-error" ]
    [ alertDanger_
        [ showAjaxError error
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError = runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err

showErrorDescription (ResponseFormatError err) = text $ "ResponseFormatError: " <> err

showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

renderForeignErrors :: MultipleErrors -> String
renderForeignErrors = intercalate "\n" <<< map renderForeignError
