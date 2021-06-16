module InputField.View (renderInput) where

import Prelude hiding (div)
import Css (classNames, hideWhen)
import Css as Css
import Data.Array (filter)
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (isJust)
import Data.String (Pattern(..), contains, toLower)
import Halogen.HTML (HTML, a, div, input, text)
import Halogen.HTML.Events.Extra (onClick_, onFocus_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), autocomplete, list, id_, placeholder, readOnly, type_, value)
import InputField.Lenses (_additionalCss, _baseCss, _datalistId, _dropdownOpen, _id_, _placeholder, _pristine, _readOnly, _value, _valueOptions)
import InputField.State (validate)
import InputField.Types (class InputFieldError, Action(..), InputDisplayOptions, State, inputErrorToString)

renderInput :: forall p e. InputFieldError e => State e -> InputDisplayOptions -> HTML p (Action e)
renderInput state options =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    dropdownOpen = view _dropdownOpen state

    showError = not pristine && isJust mError

    baseCss = view _baseCss options

    additionalCss = view _additionalCss options

    mDatalistId = view _datalistId options

    valueOptions = view _valueOptions options

    matchingValueOptions = filter (\v -> contains (Pattern $ toLower currentValue) (toLower $ v)) valueOptions
  in
    div
      [ classNames [ "relative" ] ]
      [ input
          $ [ type_ InputText
            , classNames $ (baseCss showError) <> additionalCss
            , id_ $ view _id_ options
            , placeholder $ view _placeholder options
            , value currentValue
            , readOnly $ view _readOnly options
            , autocomplete false
            , onValueInput_ SetValue
            ]
          <> if valueOptions /= mempty then
              [ autocomplete false, onFocus_ $ SetDropdownOpen true ]
            else
              []
                <> foldMap (\datalistId -> [ list datalistId ]) mDatalistId
      , div
          [ classNames
              $ [ "absolute", "z-10", "w-full", "max-h-56", "overflow-x-hidden", "overflow-y-scroll", "-mt-2", "pt-2", "bg-white", "shadow", "rounded-b" ]
              <> (hideWhen $ not dropdownOpen || matchingValueOptions /= mempty)
          ]
          (valueOptionsList <$> matchingValueOptions)
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap inputErrorToString mError else mempty ]
      ]
  where
  valueOptionsList valueOption =
    a
      [ classNames [ "block", "p-4", "hover:bg-black", "hover:text-white" ]
      , onClick_ $ SetValue valueOption
      ]
      [ text valueOption ]
