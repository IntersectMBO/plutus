module Analytics
  ( Event
  , defaultEvent
  , trackEvent
  ) where

import Effect
  ( Effect
  )
import Data.Function.Uncurried
  ( Fn4
  , runFn4
  )
import Data.Maybe
  ( Maybe(..)
  )
import Data.Undefinable
  ( Undefinable
  , toUndefinable
  )
import Data.Unit
  ( Unit
  )

foreign import trackEvent_ ::
  forall eff.
  Fn4 String (Undefinable String) (Undefinable String) (Undefinable Number) (Effect Unit)

type Event
  = {action :: String, category :: Maybe String, label :: Maybe String, value :: Maybe Number}

defaultEvent ::
  String ->
  Event
defaultEvent action = { action
                      , category: Nothing
                      , label: Nothing
                      , value: Nothing
                      }

trackEvent ::
  forall eff.
  Event ->
  Effect Unit
trackEvent { action, category, label, value } = runFn4 trackEvent_ action (toUndefinable category) (toUndefinable label) (toUndefinable value)
