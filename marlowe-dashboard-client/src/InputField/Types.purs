module InputField.Types
  ( State
  , class InputFieldError
  , inputErrorToString
  , Action(..)
  , InputDisplayOptions
  ) where

import Analytics (class IsEvent)
import Data.Maybe (Maybe(..))
import Marlowe.Extended.Metadata (NumberFormat)

type State error
  = { value :: String -- all values are strings in JavaScript; embrace it
    , pristine :: Boolean
    , validator :: String -> Maybe error
    , dropdownOpen :: Boolean
    -- This is a bit fiddly. We want the dropdown to close when the input element loses focus (onBlur).
    -- But when we click on a valueOption in the dropdown, we want to set the value to that option, and
    -- initially I couldn't get this to work because the onBlur event listener was getting in the way.
    -- There might be a more idiomatic solution with stopPropagation, but I tried a few things with that
    -- and nothing seemed to work. In the end I added this flag, which is set to true onMouseEnter for
    -- the dropdown (and false again onMouseLeave) - and if it's true, we shortcircuit the onBlur (and
    -- the handler for SetValueFromDropdown closes the dropdown instead). Maybe not the nicest solution,
    -- but it works.
    , dropdownLocked :: Boolean
    }

class InputFieldError e where
  inputErrorToString :: e -> String

-- TODO: should the validator be in the InputDisplayOptions instead of the State?
type InputDisplayOptions
  = { baseCss :: Boolean -> Array String
    , additionalCss :: Array String
    , id_ :: String
    , placeholder :: String
    , readOnly :: Boolean
    , numberFormat :: Maybe NumberFormat -- set to nothing for string inputs
    , valueOptions :: Array String -- non-empty for select inputs
    }

data Action error
  = SetValue String
  | SetValueFromDropdown String
  | FormatValue NumberFormat
  | SetValidator (String -> Maybe error)
  | SetDropdownOpen Boolean
  | SetDropdownLocked Boolean
  | Reset

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent (Action e) where
  toEvent action = Nothing
