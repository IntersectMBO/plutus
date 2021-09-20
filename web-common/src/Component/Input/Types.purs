module Component.Input.Types
  ( InputType(..)
  , Input
  ) where

import Data.Maybe (Maybe)

data InputType
  = Text
  | Numeric

type Input action
  = { autocomplete :: Boolean
    , id :: String
    , inputType :: InputType
    , invalid :: Boolean
    , noHighlight :: Boolean
    , onBlur :: Maybe action
    , onChange :: Maybe (String -> action)
    , onFocus :: Maybe action
    , placeholder :: String
    , value :: String
    }
