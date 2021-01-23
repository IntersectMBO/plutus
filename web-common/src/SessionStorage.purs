module SessionStorage where

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Prelude
import LocalStorage (Key)

foreign import _setItem :: EffectFn2 Key String Unit

foreign import _getItem :: EffectFn1 Key (Nullable String)

setItem :: Key -> String -> Effect Unit
setItem = runEffectFn2 _setItem

getItem :: Key -> Effect (Maybe String)
getItem = map toMaybe <$> runEffectFn1 _getItem
