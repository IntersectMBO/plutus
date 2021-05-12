module InputField.View (renderInput) where

import Prelude hiding (div)
import Css (classNames)
import Css as Css
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (isJust)
import Halogen.HTML (HTML, div, div_, input, text)
import Halogen.HTML.Events.Extra (onValueInput_)
import Halogen.HTML.Properties (InputType(..), autocomplete, id_, placeholder, readOnly, type_, value)
import InputField.Lenses (_additionalCss, _baseCss, _id_, _placeholder, _pristine, _readOnly, _value)
import InputField.State (validate)
import InputField.Types (Action(..), InputDisplayOptions, State)

renderInput :: forall p e. Show e => State e -> InputDisplayOptions -> HTML p (Action e)
renderInput state options =
  let
    mError = validate state

    pristine = view _pristine state

    showError = not pristine && isJust mError

    baseCss = view _baseCss options

    additionalCss = view _additionalCss options
  in
    div_
      [ input
          [ type_ InputText
          , classNames $ (baseCss showError) <> additionalCss
          , id_ $ view _id_ options
          , placeholder $ view _placeholder options
          , value $ view _value state
          , readOnly $ view _readOnly options
          , autocomplete false
          , onValueInput_ SetValue
          ]
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap show mError else mempty ]
      ]
