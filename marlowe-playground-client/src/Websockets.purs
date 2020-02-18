module Websockets where

import Prelude
import Control.Coroutine (Producer, Consumer)
import Control.Coroutine as CR
import Control.Coroutine.Aff (emit, produce)
import Control.Monad.Except (runExcept)
import Data.Either (hush)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Foreign (Foreign, F, readString)
import Types (HQuery(..), Message(..))
import Web.Event.EventTarget (addEventListener, eventListener)
import Web.Socket.Event.EventTypes (onMessage)
import Web.Socket.Event.MessageEvent as MessageEvent
import Web.Socket.WebSocket (WebSocket)
import Web.Socket.WebSocket as WS

wsProducer :: WebSocket -> Producer String Aff Unit
wsProducer socket =
  produce \emitter -> do
    listener <-
      eventListener \ev -> do
        for_ (MessageEvent.fromEvent ev) \msgEvent ->
          for_ (readHelper readString (MessageEvent.data_ msgEvent)) \msg ->
            emit emitter msg
    addEventListener onMessage listener false (WS.toEventTarget socket)
  where
  readHelper :: forall a. (Foreign -> F a) -> Foreign -> Maybe a
  readHelper reader = hush <<< runExcept <<< reader

wsConsumer :: (forall a. HQuery a -> Aff (Maybe a)) -> Consumer String Aff Unit
wsConsumer query =
  CR.consumer \msg -> do
    void $ query $ ReceiveWebsocketMessage msg unit
    pure Nothing

wsSender :: WebSocket -> Consumer Message Aff Unit
wsSender socket =
  CR.consumer
    $ \msg -> do
        case msg of
          WebsocketMessage contents -> void $ liftEffect $ WS.sendString socket contents
        pure Nothing
