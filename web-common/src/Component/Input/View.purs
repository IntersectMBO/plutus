module Component.Input.View
  ( defaultInput
  , renderWithChildren
  , render
  ) where

import Prelude
import Component.Input.Types (Input, InputType(..))
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Traversable (sequence)
import Halogen as H
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

defaultInput :: forall action. Input action
defaultInput =
  { autocomplete: false
  , id: ""
  , inputType: Text
  , invalid: false
  , noHighlight: false
  , onBlur: Nothing
  , onChange: Nothing
  , onFocus: Nothing
  , placeholder: ""
  , value: ""
  }

render :: forall w action. Input action -> HH.HTML w action
render input = renderWithChildren input pure

renderWithChildren ::
  forall w action.
  Input action ->
  (HH.HTML w action -> Array (HH.HTML w action)) ->
  HH.HTML w action
renderWithChildren input renderChildren =
  HH.div
    [ classNames containerStyles ]
    $ renderChildren
    $ HH.input
    $ [ classNames inputStyles
      , HP.id_ input.id
      , HP.ref $ H.RefLabel input.id
      , HP.placeholder input.placeholder
      , HP.autocomplete input.autocomplete
      , HP.value input.value
      , HP.readOnly $ isNothing input.onChange
      , HP.tabIndex $ maybe (-1) (const 0) input.onChange
      , HE.onValueInput $ sequence input.onChange
      , HE.onBlur $ const input.onBlur
      , HE.onFocus $ const input.onFocus
      , HP.type_ case input.inputType of
          Text -> HP.InputText
          Numeric -> HP.InputNumber
      ]
  where
  containerStyles =
    [ "border-2"
    , "duration-200"
    , "flex"
    , "gap-1"
    , "items-baseline"
    , "p-4"
    , "relative"
    , "rounded-sm"
    , "transition-all"
    , "w-full"
    ]
      <> if input.noHighlight || isNothing input.onChange then
          [ if input.invalid then "border-red" else "border-gray" ]
        else
          [ "focus:border-transparent"
          , "focus:ring-2"
          , "focus-within:border-transparent"
          , "focus-within:ring-2"
          ]
            <> if input.invalid then
                [ "border-red", "ring-red" ]
              else
                [ "border-gray", "ring-purple" ]

  inputStyles =
    [ "border-0"
    , "duration-200"
    , "flex-1"
    , "focus:outline-none"
    , "focus:ring-0"
    , "leading-none"
    , "outline-none"
    , "p-0"
    , "ring-0"
    , "text-black"
    , "transition-all"
    ]
