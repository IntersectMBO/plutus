module InputField.Types
  ( State
  , class InputFieldError
  , inputErrorToString
  , Action(..)
  , InputDisplayOptions
  ) where

import Analytics (class IsEvent)
import Data.Maybe (Maybe(..))

type State error
  = { value :: String
    , pristine :: Boolean
    , validator :: String -> Maybe error
    , dropdownOpen :: Boolean
    }

class InputFieldError e where
  inputErrorToString :: e -> String

type InputDisplayOptions
  = { baseCss :: Boolean -> Array String
    , additionalCss :: Array String
    , id_ :: String
    , placeholder :: String
    , readOnly :: Boolean
    , datalistId :: Maybe String
    , valueOptions :: Array String
    }

data Action error
  = SetValue String
  | SetValidator (String -> Maybe error)
  | SetDropdownOpen Boolean
  | Reset

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent (Action e) where
  toEvent (SetValue _) = Nothing
  toEvent (SetValidator _) = Nothing
  toEvent (SetDropdownOpen _) = Nothing
  toEvent Reset = Nothing
