module InputField.Types
  ( State
  , Action(..)
  , InputDisplayOptions
  ) where

import Analytics (class IsEvent)
import Data.Maybe (Maybe(..))

type State error
  = { value :: String
    , pristine :: Boolean
    , validator :: String -> Maybe error
    }

type InputDisplayOptions
  = { baseCss :: Boolean -> Array String
    , additionalCss :: Array String
    , id_ :: String
    , placeholder :: String
    , readOnly :: Boolean
    }

data Action error
  = SetValue String
  | SetValidator (String -> Maybe error)
  | Reset

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent (Action e) where
  toEvent (SetValue _) = Nothing
  toEvent (SetValidator _) = Nothing
  toEvent Reset = Nothing
