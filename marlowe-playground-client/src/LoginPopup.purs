module LoginPopup where

import Prelude

import Auth (AuthRole(..), AuthStatus(..), authStatusAuthRole)
import Control.Monad.Except (runExcept)
import Control.Promise (Promise, toAffE)
import Data.Either (Either(..), hush)
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Debug.Trace (traceM)
import Effect (Effect)
import Effect.Aff (Aff, bracket, makeAff, never, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Uncurried as FU
import Foreign (Foreign)
import Foreign.Generic.Class (encode, decode)
import Network.RemoteData (RemoteData(..))
import Types (WebData)
import Web.Event.Event (EventType(..), Event)
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener)
import Web.HTML as Web
import Web.HTML.Window (open, opener, outerHeight, outerWidth)
import Web.HTML.Window as WebWindow
import Web.HTML.WindowExtra (close, postMessage)
import Web.Socket.Event.MessageEvent as MessageEvent

foreign import _openLoginPopup :: FU.EffectFn1 Unit (Promise Boolean)

-- TODO: the open login is sync, should we use an Effect and then trigger an Action
-- in the MainFrame when the login succeds? or should we use an Aff to expect eventual
-- response (LogedIn | Error | Cancel)
openLoginPopup' :: Aff Boolean
openLoginPopup' = toAffE $ FU.runEffectFn1 _openLoginPopup unit

openLoginPopup :: Aff AuthRole
openLoginPopup = do
  let
    popupHeight = 620

    popupWidth = 600

    features :: Effect String
    features = do
      window <- Web.window
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

    -- I have:
    -- eventListener :: forall a. (Event -> Effect a) -> Effect EventListener
    -- addEventListener :: EventType -> EventListener -> Boolean -> EventTarget -> Effect Unit
    -- removeEventListener :: EventType -> EventListener -> Boolean -> EventTarget -> Effect Unit
    --
    -- makeAff :: forall a. ((Either Error a -> Effect Unit) -> Effect Canceler) -> Aff a
    -- never :: forall a. Aff a
    -- bracket :: forall a b. Aff a -> (a -> Aff Unit) -> (a -> Aff b) -> Aff b

    -- I need: Aff Boolean

    decodeMessageEvent :: Event -> Maybe AuthRole
    decodeMessageEvent event = do
      data' <- MessageEvent.data_ <$> MessageEvent.fromEvent event
      hush <<< runExcept <<< decode $ data'

    -- TODO: in this version I cant clean the event listener
    waitForEvent2 :: Aff AuthRole
    waitForEvent2 = makeAff resolver where
      -- resolver :: ((Either Error a -> Effect Unit) -> Effect Canceler)
      resolver cb = do
        window <- Web.window
        listener <- eventListener \event -> do
          log $ "waitForEvent2 event listener "
          traceM event

          case decodeMessageEvent event  of
            Nothing -> pure unit
            Just role -> cb $ Right role

        addEventListener (EventType "message") listener false $ WebWindow.toEventTarget window
        pure nonCanceler

    -- TODO: in this version I cant get the value out
    waitForEvent3 :: Aff Boolean
    waitForEvent3 = bracket acquire release produce where
      -- acquire :: Aff EventListener
      acquire = liftEffect do
        window <- Web.window
        listener <- eventListener \event -> do
          log $ "waitForEvent3 event listener "
          traceM event
          pure unit
          -- case decodeMessageEvent event  of
          --   Nothing -> pure unit
          --   Just str -> case str of
          --     "GithubUser" -> cb $ Right true
          --     "Anonymous" -> cb $ Right false
          --     _ -> pure unit

        addEventListener (EventType "message") listener false (WebWindow.toEventTarget window)
        pure listener
      -- release :: EventListener -> Aff Unit
      release listener = liftEffect $ do
        window <- Web.window
        removeEventListener (EventType "message") listener false (WebWindow.toEventTarget window)

      -- produce :: EventListener -> Aff Boolean
      produce _ = pure false

    -- waitForEvent :: Aff Boolean
    -- waitForEvent = bracket
    --   (eventListener )

    popup :: Effect Unit
    popup = do
      ft <- features
      window <- Web.window
      -- _ <- open "/" "_blank" ft window
      _ <- open "/api/oauth/github" "_blank" ft window
      pure unit
  liftEffect popup
  -- never
  waitForEvent2

-- TODO: Move the WebData part to the route handling and rename as informParentAndClose
informParentIfPresentAndClose :: WebData AuthStatus -> Effect Unit
informParentIfPresentAndClose (Success authStatus) = do
  let
    authRole = view authStatusAuthRole authStatus
  window <- Web.window
  maybeParent <- opener window
  for_ maybeParent \parent -> do
    postMessage (encode authRole) parent
    close window

informParentIfPresentAndClose _ = pure unit
