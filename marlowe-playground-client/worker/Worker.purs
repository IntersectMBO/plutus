module Worker where

import Prelude

import Data.Function.Uncurried (Fn0, Fn1, Fn2, runFn0, runFn1, runFn2)
import Effect (Effect)
import Effect.Class.Console (log)

foreign import data Context :: Type
foreign import data MessageEvent :: Type
foreign import registerOnMessage :: Fn2 Context (MessageEvent -> Unit) Unit
foreign import context :: Fn0 Context
foreign import handler :: Fn1 MessageEvent Unit

main ::
  Effect Unit
main = do
    ctx <- pure $ runFn0 context
    h <- pure $ runFn1 handler
    let x = runFn2 registerOnMessage ctx h
    log "hi"

f :: Int -> Int
f x = x + 1