module Worker where

import Prelude

import Effect (Effect)
import Effect.Class.Console (log)

foreign import onmessage :: Unit

main ::
  Effect Unit
main = do
    log "hi"

f :: Int -> Int
f x = x + 1