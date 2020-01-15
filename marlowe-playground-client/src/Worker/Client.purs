module Worker.Client where

import Prelude
import Control.Coroutine (Producer, Consumer)
import Control.Coroutine as CR
import Control.Coroutine.Aff (emit, produce)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Uncurried (EffectFn2, runEffectFn2)
import Foreign (Foreign)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Types (HQuery(..))
import Worker.Types (WorkerRequest, WorkerResponse)

foreign import data Worker :: Type

foreign import spawn :: Effect Worker

foreign import postMessage_ :: EffectFn2 Worker Foreign Unit

foreign import registerOnMessage_ :: EffectFn2 Worker (Foreign -> Effect Unit) Unit

postMessage :: Worker -> WorkerRequest -> Effect Unit
postMessage worker req =
  let
    msg = genericEncode defaultOptions req
  in
    runEffectFn2 postMessage_ worker msg

registerOnMessage :: Worker -> (WorkerResponse -> Effect Unit) -> Effect Unit
registerOnMessage worker f = do
  runEffectFn2 registerOnMessage_ worker handler
  where
  handler msg = case runExcept (genericDecode defaultOptions msg) of
    Left err -> pure unit
    Right resp -> f resp

wsProducer :: Worker -> Producer WorkerResponse Aff Unit
wsProducer worker =
  produce \emitter -> do
    let
      listener resp = emit emitter resp
    registerOnMessage worker listener

wsConsumer :: (forall a. HQuery a -> Aff (Maybe a)) -> Consumer WorkerResponse Aff Unit
wsConsumer query =
  CR.consumer \msg -> do
    void $ query $ ReceiveWorkerMessage msg unit
    pure Nothing

wsSender :: Worker -> Consumer WorkerRequest Aff Unit
wsSender worker =
  CR.consumer
    $ \msg -> do
        void $ liftEffect $ postMessage worker msg
        pure Nothing
