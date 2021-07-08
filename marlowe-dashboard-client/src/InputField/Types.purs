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

type InputDisplayOptions
  = { baseCss :: Boolean -> Array String
    , additionalCss :: Array String
    , id_ :: String
    , placeholder :: String
    , readOnly :: Boolean
    , valueOptions :: Array String
    }

data Action error
  = SetValue String
  | SetValueFromDropdown String
  | SetValidator (String -> Maybe error)
  | SetDropdownOpen Boolean
  | SetDropdownLocked Boolean
  | Reset

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent (Action e) where
  toEvent (SetValue _) = Nothing
  toEvent (SetValueFromDropdown _) = Nothing
  toEvent (SetValidator _) = Nothing
  toEvent (SetDropdownOpen _) = Nothing
  toEvent (SetDropdownLocked _) = Nothing
  toEvent Reset = Nothing
