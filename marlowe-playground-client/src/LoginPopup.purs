module LoginPopup where

import Prelude

import Auth (AuthRole)
import Control.Monad.Except (runExcept)
import Data.Either (Either(..), hush)
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Aff (Aff, finally, makeAff, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Generic.Class (encode, decode)
import Web.Event.Event (Event, EventType(..))
import Web.Event.EventTarget (EventListener, addEventListener, eventListener, removeEventListener)
import Web.HTML as Web
import Web.HTML.Location (replace, origin)
import Web.HTML.Window (outerHeight, outerWidth)
import Web.HTML.Window as Window
import Web.HTML.WindowExtra (close, postMessage)
import Web.Socket.Event.MessageEvent as MessageEvent

-- This function is intended to be called between a parent window. It creates a popup to the
-- the Github auth page and waits for the popup to send a message with the current AuthRole
openLoginPopup :: Aff AuthRole
openLoginPopup = do
  window <- liftEffect Web.window
  let
    popupHeight = 620

    popupWidth = 600

    githubLoginPage = "/api/oauth/github"

    features :: Effect String
    features = do
        top <-
          outerHeight window
            <#> \windowHeight -> windowHeight / 2 - popupHeight / 2
        left <-
          outerWidth window
            <#> \windowWidth -> windowWidth / 2 - popupWidth / 2
        pure $ "width="
          <> show popupWidth
          <> ",height="
          <> show popupHeight
          <> ",top="
          <> show top
          <> ",left="
          <> show left
          <> ",menubar=no,status=no,location=no"

    decodeMessageEvent :: Event -> Maybe AuthRole
    decodeMessageEvent event = do
      data' <- MessageEvent.data_ <$> MessageEvent.fromEvent event
      hush <<< runExcept <<< decode $ data'

    messageEvent = EventType "message"

    windowEventTarget = Window.toEventTarget window

    waitForEvent :: Ref (Maybe EventListener) -> Aff AuthRole
    waitForEvent listenerRef = makeAff resolver
      where
      resolver cb = do
        -- This callback listens for all "message" events, but only succeeds when
        -- we can decode the event.data as an AuthRole
        listener <-
          eventListener \event -> case decodeMessageEvent event of
            Nothing -> pure unit
            Just role -> cb $ Right role
        Ref.write (Just listener) listenerRef
        addEventListener messageEvent listener false windowEventTarget
        -- We can return a nonCanceler because the waitForEvent is called with a finally
        pure nonCanceler

    removeWaitForEventListener :: Ref (Maybe EventListener) -> Effect Unit
    removeWaitForEventListener listenerRef = do
        mbListener <- Ref.read listenerRef
        for_ mbListener \listener ->
          removeEventListener messageEvent listener false windowEventTarget
  featureString <- liftEffect $ features
  _ <- liftEffect $ Window.open githubLoginPage "_blank" featureString window
  listenerRef <- liftEffect $ Ref.new Nothing
  -- Make sure that the event listener is removed no matter what
  finally
    (liftEffect $ removeWaitForEventListener listenerRef)
    (waitForEvent listenerRef)

-- This function is intended to be called from the popup window created by openLoginPopup.
informParentAndClose :: AuthRole -> Effect Unit
informParentAndClose authRole = do
  window <- Web.window
  location <- Window.location window
  targetOrigin <- origin location
  Window.opener window
    >>= case _ of
        -- If the function is called from a poput window (expected behaviour)
        -- then we comunicate the login result with our parent window and close
        -- the popup
        Just parent -> do
          postMessage (encode authRole) targetOrigin parent
          close window
        -- If someone access the github callback url directly, we redirect them to
        -- the home page
        Nothing ->  replace "/" location
