module AjaxUtils
  ( AjaxErrorPaneAction(..)
  , ajaxErrorPane
  , closeableAjaxErrorPane
  , ajaxErrorRefLabel
  , renderForeignErrors
  , defaultJsonOptions
  ) where

import Prelude hiding (div)
import Bootstrap (alertDanger_, btn, floatRight)
import Data.Foldable (intercalate)
import Data.Maybe (Maybe(Just))
import Foreign (MultipleErrors, renderForeignError)
import Foreign.Generic.Class (Options, aesonSumEncoding, defaultOptions)
import Halogen (RefLabel(RefLabel))
import Halogen.HTML (ClassName(..), HTML, br_, button, div, p_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, ref)
import Icons (Icon(..), icon)
import Servant.PureScript.Ajax (AjaxError, ErrorDescription(..), runAjaxError)

data AjaxErrorPaneAction
  = CloseErrorPane

ajaxErrorPane :: forall p i. AjaxError -> HTML p i
ajaxErrorPane error =
  div
    [ class_ ajaxErrorClass
    , ref ajaxErrorRefLabel
    ]
    [ alertDanger_
        [ showAjaxError error
        , br_
        , text "Please try again or contact support for assistance."
        ]
    ]

closeableAjaxErrorPane :: forall p. AjaxError -> HTML p AjaxErrorPaneAction
closeableAjaxErrorPane error =
  div
    [ class_ ajaxErrorClass ]
    [ alertDanger_
        [ button
            [ classes [ btn, floatRight, ClassName "ajax-error-close-button" ]
            , onClick $ const $ Just CloseErrorPane
            ]
            [ icon Close ]
        , p_ [ showAjaxError error ]
        ]
    ]

ajaxErrorRefLabel :: RefLabel
ajaxErrorRefLabel = RefLabel "ajax-error"

ajaxErrorClass :: ClassName
ajaxErrorClass = ClassName "ajax-error"

showAjaxError :: forall p i. AjaxError -> HTML p i
showAjaxError = runAjaxError >>> _.description >>> showErrorDescription

showErrorDescription :: forall p i. ErrorDescription -> HTML p i
showErrorDescription NotFound = text "Data not found."

showErrorDescription (ResponseError statusCode err) = text $ "Server error " <> show statusCode <> ": " <> err

showErrorDescription (DecodingError err@"(\"Unexpected token E in JSON at position 0\" : Nil)") = text "Cannot connect to the server. Please check your network connection."

showErrorDescription (DecodingError err) = text $ "DecodingError: " <> err

showErrorDescription (ResponseFormatError err) = text $ "ResponseFormatError: " <> err

showErrorDescription (ConnectionError err) = text $ "ConnectionError: " <> err

renderForeignErrors :: MultipleErrors -> String
renderForeignErrors = intercalate "\n" <<< map renderForeignError

defaultJsonOptions :: Options
defaultJsonOptions =
  defaultOptions
    { unwrapSingleConstructors = true
    , sumEncoding = aesonSumEncoding
    }
