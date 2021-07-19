module InputField.View (renderInput) where

import Prelude hiding (div, min)
import Css as Css
import Data.Array (filter)
import Data.Foldable (foldMap)
import Data.Lens (view)
import Data.Maybe (Maybe(..), isJust)
import Data.String (Pattern(..), contains, toLower)
import Halogen.Css (classNames)
import Halogen.HTML (HTML, a, div, div_, input, span_, text)
import Halogen.HTML.Events (onBlur, onMouseEnter, onMouseLeave)
import Halogen.HTML.Events.Extra (onBlur_, onClick_, onFocus_, onValueInput_)
import Halogen.HTML.Properties (InputType(..), autocomplete, id_, placeholder, readOnly, type_, value)
import InputField.Lenses (_additionalCss, _dropdownLocked, _dropdownOpen, _id_, _placeholder, _pristine, _readOnly, _value)
import InputField.State (validate)
import InputField.Types (class InputFieldError, Action(..), InputDisplayOptions, State, inputErrorToString)
import Marlowe.Extended.Metadata (NumberFormat(..))

renderInput :: forall p e. InputFieldError e => InputDisplayOptions -> State e -> HTML p (Action e)
renderInput options@{ numberFormat: Nothing, valueOptions: [] } state =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    showError = not pristine && isJust mError

    additionalCss = view _additionalCss options
  in
    div_
      [ input
          $ [ type_ InputText
            , classNames $ (Css.input $ not showError) <> additionalCss
            , id_ $ view _id_ options
            , placeholder $ view _placeholder options
            , value currentValue
            , readOnly $ view _readOnly options
            , autocomplete false
            , onValueInput_ SetValue
            ]
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap inputErrorToString mError else mempty ]
      ]

renderInput options@{ numberFormat: Nothing, valueOptions } state =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    dropdownOpen = view _dropdownOpen state

    dropdownLocked = view _dropdownLocked state

    showError = not pristine && isJust mError

    additionalCss = view _additionalCss options

    matchingValueOptions = filter (\v -> contains (Pattern $ toLower currentValue) (toLower v)) valueOptions
  in
    div
      [ classNames [ "relative" ] ]
      [ input
          $ [ type_ InputText
            , classNames $ (Css.inputNoFocus $ not showError) <> additionalCss
            , id_ $ view _id_ options
            , placeholder $ view _placeholder options
            , value currentValue
            , readOnly $ view _readOnly options
            , autocomplete false
            , onValueInput_ SetValue
            ]
          <> if valueOptions /= mempty then
              [ autocomplete false
              , onFocus_ $ SetDropdownOpen true
              , onBlur $ const $ if dropdownLocked then Nothing else Just $ SetDropdownOpen false
              ]
            else
              []
      , div
          [ classNames $ Css.pseudoDropdown (dropdownOpen && matchingValueOptions /= mempty)
          , onMouseEnter $ const $ Just $ SetDropdownLocked true
          , onMouseLeave $ const $ Just $ SetDropdownLocked false
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
      , onClick_ $ SetValueFromDropdown valueOption
      ]
      [ text valueOption ]

renderInput options@{ numberFormat: Just DefaultFormat } state =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    showError = not pristine && isJust mError

    additionalCss = view _additionalCss options
  in
    div_
      [ input
          $ [ type_ InputNumber
            , classNames $ (Css.input $ not showError) <> additionalCss
            , id_ $ view _id_ options
            , value currentValue
            , readOnly $ view _readOnly options
            , autocomplete false
            , onValueInput_ SetValue
            ]
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap inputErrorToString mError else mempty ]
      ]

renderInput options@{ numberFormat: Just TimeFormat } state =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    showError = not pristine && isJust mError

    additionalCss = view _additionalCss options
  in
    div_
      [ div
          [ classNames $ Css.input (not showError) <> additionalCss <> [ "flex", "gap-1", "items-baseline" ] ]
          [ input
              [ type_ InputNumber
              , classNames $ Css.unstyledInput <> [ "flex-1" ]
              , id_ $ view _id_ options
              , value currentValue
              , readOnly $ view _readOnly options
              , autocomplete false
              , onValueInput_ SetValue
              , onBlur_ $ FormatValue TimeFormat
              ]
          , span_
              [ text "minutes" ]
          ]
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap inputErrorToString mError else mempty ]
      ]

renderInput options@{ numberFormat: Just (DecimalFormat decimals label) } state =
  let
    mError = validate state

    currentValue = view _value state

    pristine = view _pristine state

    showError = not pristine && isJust mError

    additionalCss = view _additionalCss options
  in
    div_
      [ div
          [ classNames $ Css.input (not showError) <> additionalCss <> [ "flex", "gap-1", "items-baseline" ] ]
          [ span_
              [ text label ]
          , input
              [ type_ InputNumber
              , classNames $ Css.unstyledInput <> [ "flex-1" ]
              , id_ $ view _id_ options
              , value currentValue
              , readOnly $ view _readOnly options
              , autocomplete false
              , onValueInput_ SetValue
              , onBlur_ $ FormatValue $ DecimalFormat decimals label
              ]
          ]
      , div
          [ classNames Css.inputError ]
          [ text if showError then foldMap inputErrorToString mError else mempty ]
      ]
