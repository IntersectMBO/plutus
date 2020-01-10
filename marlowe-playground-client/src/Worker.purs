module Worker where

import Prelude

import Effect (Effect)
import Effect.Uncurried (EffectFn2, runEffectFn2)

foreign import data Worker :: Type

foreign import spawn :: Effect Worker

foreign import analyseContract_ :: EffectFn2 Worker String Unit

analyseContract :: Worker -> String -> Effect Unit
analyseContract = runEffectFn2 analyseContract_