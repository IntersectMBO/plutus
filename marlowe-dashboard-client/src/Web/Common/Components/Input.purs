module Web.Common.Components.Input
  ( InputType(..)
  , Params
  , render
  , defaultParams
  ) where

import Prelude
import Css as Css
import Data.Array (fromFoldable)
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Traversable (sequence)
import Halogen as H
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-------------------------------------------------------------------------------
-- Public API types
-------------------------------------------------------------------------------
data InputType
  = Text
  | Numeric

type Params w i
  = { after :: Maybe (HH.HTML w i)
    , autocomplete :: Boolean
    , before :: Maybe (HH.HTML w i)
    , id :: String
    , inputType :: InputType
    , invalid :: Boolean
    , noHighlight :: Boolean
    , onBlur :: Maybe i
    , onChange :: Maybe (String -> i)
    , onFocus :: Maybe i
    , placeholder :: String
    , value :: String
    }

-------------------------------------------------------------------------------
-- Public API
-------------------------------------------------------------------------------
defaultParams :: forall w i. Params w i
defaultParams =
  { after: Nothing
  , autocomplete: false
  , before: Nothing
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

render :: forall w i. Params w i -> HH.HTML w i
render params =
  HH.div
    [ classNames containerStyles ]
    $ fromFoldable params.before
    <> [ HH.input
          ( [ classNames inputStyles
            , HP.id_ params.id
            , HP.ref $ H.RefLabel params.id
            , HP.placeholder params.placeholder
            , HP.autocomplete params.autocomplete
            , HP.value params.value
            , HP.readOnly $ isNothing params.onChange
            , HP.tabIndex $ maybe (-1) (const 0) params.onChange
            , HE.onValueInput $ sequence params.onChange
            , HP.type_ case params.inputType of
                Text -> HP.InputText
                Numeric -> HP.InputNumber
            ]
          )
      ]
    <> fromFoldable params.after
  where
  containerStyles =
    [ "flex"
    , "items-baseline"
    , "w-full"
    , "p-4"
    , "gap-1"
    , "rounded-sm"
    , "border-2"
    , "relative"
    ]
      <> Css.withAnimation
      <> if params.noHighlight || isNothing params.onChange then
          [ if params.invalid then "border-red" else "border-gray" ]
        else
          [ "focus:border-transparent"
          , "focus:ring-2"
          , "focus-within:border-transparent"
          , "focus-within:ring-2"
          ]
            <> if params.invalid then
                [ "border-red", "ring-red" ]
              else
                [ "border-gray", "ring-purple" ]

  inputStyles =
    [ "flex-1"
    , "p-0"
    , "border-0"
    , "outline-none"
    , "focus:outline-none"
    , "ring-0"
    , "focus:ring-0"
    , "leading-none"
    , "text-black"
    ]
      <> Css.withAnimation
