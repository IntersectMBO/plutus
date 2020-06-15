module WebSocket.Support where

import Prelude
import Control.Coroutine (Producer, Consumer)
import Control.Coroutine as CR
import Control.Coroutine.Aff (emit, produce)
import Control.Monad.Except (runExcept)
import Data.Either (Either)
import Data.Foldable (for_)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Foreign (MultipleErrors, F)
import Foreign.Class (class Decode, class Encode, decode)
import Foreign.Generic (decodeJSON, encodeJSON)
import Web.Event.EventTarget (addEventListener, eventListener)
import Web.HTML as W
import Web.HTML.Location as WL
import Web.HTML.Window as WW
import Web.Socket.Event.EventTypes (onMessage)
import Web.Socket.Event.MessageEvent as MessageEvent
import Web.Socket.ReadyState as WSRS
import Web.Socket.WebSocket (WebSocket)
import Web.Socket.WebSocket as WS

data Output a
  = ReceiveMessage (Either MultipleErrors a)
  | WebSocketClosed

derive instance genericOutput :: Generic (Output a) _

instance showOutput :: Show a => Show (Output a) where
  show = genericShow

data Input a
  = SendMessage a

derive instance genericInput :: Generic (Input a) _

instance showInput :: Show a => Show (Input a) where
  show = genericShow

------------------------------------------------------------
mkSocket :: String -> Effect WebSocket
mkSocket uri = do
  window <- W.window
  location <- WW.location window
  protocol <- WL.protocol location
  hostname <- WL.hostname location
  port <- WL.port location
  let
    wsProtocol = case protocol of
      "https:" -> "wss"
      _ -> "ws"

    wsPath = wsProtocol <> "://" <> hostname <> ":" <> port <> uri
  WS.create wsPath []

------------------------------------------------------------
wsProducer ::
  forall a.
  Decode a =>
  WebSocket -> Producer (Output a) Aff Unit
wsProducer socket =
  produce \emitter -> do
    listener <-
      eventListener \ev -> do
        for_ (MessageEvent.fromEvent ev) \msgEvent ->
          let
            decoder :: F a
            decoder = do
              str <- decode $ MessageEvent.data_ msgEvent
              decodeJSON str
          in
            emit emitter $ ReceiveMessage $ runExcept decoder
    addEventListener onMessage listener false (WS.toEventTarget socket)

wsConsumer :: forall m a. Monad m => (a -> m Unit) -> Consumer a m Unit
wsConsumer query =
  CR.consumer \msg -> do
    query msg
    pure Nothing

wsSender ::
  forall m a b c r.
  Encode c =>
  MonadEffect m =>
  (Output b -> m a) ->
  WebSocket -> Consumer (Input c) m r
wsSender query socket =
  CR.consumer
    $ \msg -> do
        case msg of
          SendMessage contents -> do
            state <- liftEffect $ WS.readyState socket
            if state == WSRS.Open then
              void $ liftEffect $ WS.sendString socket $ encodeJSON contents
            else
              void $ query $ WebSocketClosed
        pure Nothing
