module LoadingSubmitButton.State (loadingSubmitButton) where

import Prelude
import Control.Monad.Cont (lift)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Int (round)
import Data.Lens (assign, set, use)
import Data.Maybe (Maybe(..))
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)
import Halogen (Component, HalogenM, Slot, getHTMLElementRef, liftEffect, mkComponent, modify_, raise)
import Halogen as H
import Halogen.Animation (waitForAllAnimations)
import Halogen.HTML (ComponentHTML, HTML, slot)
import LoadingSubmitButton.Lenses (_buttonHeight, _caption, _enabled, _status, _styles)
import LoadingSubmitButton.Types (Action(..), Input, Message(..), Query(..), State, _submitButtonSlot, buttonRef)
import LoadingSubmitButton.View (render)
import Network.RemoteData (RemoteData(..), fromEither)
import Web.DOM.DOMTokenList as DOMTokenList
import Web.DOM.Element (removeAttribute, setAttribute)
import Web.HTML.HTMLElement (classList, offsetHeight, toElement)

loadingSubmitButton ::
  forall slots m action.
  MonadAff m =>
  { ref :: String
  , styles :: Array String
  , enabled :: Boolean
  , caption :: String
  , handler :: (Message -> Maybe action)
  } ->
  ComponentHTML action ( submitButtonSlot :: Slot Query Message String | slots ) m
loadingSubmitButton { ref, styles, enabled, caption, handler } =
  slot
    _submitButtonSlot
    ref
    component
    { styles, caption, enabled }
    handler

initialState :: Input -> State
initialState { caption
, styles
, enabled
} =
  { caption
  , styles
  , enabled
  , status: NotAsked
  , buttonHeight: 0.0
  }

component ::
  forall m.
  MonadAff m =>
  Component HTML Query Input Message m
component =
  mkComponent
    { initialState
    , render
    , eval:
        H.mkEval
          $ H.defaultEval
              { handleAction = handleAction
              , handleQuery = handleQuery
              , receive = Just <<< OnNewInput
              }
    }

roundShow :: Number -> String
roundShow = show <<< round

handleAction ::
  forall m slots.
  MonadAff m =>
  Action ->
  HalogenM State Action slots Message m Unit
handleAction Submit = do
  void
    $ runMaybeT do
        -- When the user clicks on the submit button we set the Loading state,
        -- which will prepare the DOM to be a circle. We measure the height
        -- before this happens so that it stays consistent before loading, while
        -- loading and when showing the result. The final tweak that makes it a
        -- circule is to then set the same width and height via the style property.
        buttonElem <- MaybeT $ getHTMLElementRef buttonRef
        buttonHeight <- MaybeT $ map pure $ liftEffect $ offsetHeight buttonElem
        modify_
          $ set _status Loading
          <<< set _buttonHeight buttonHeight
        let
          styleStr = "width: " <> roundShow buttonHeight <> "px; height: " <> roundShow buttonHeight <> "px"
        liftEffect $ setAttribute "style" styleStr $ toElement buttonElem
        -- After we set the width of the property we are going to have a transition animation
        -- so we wait for that before adding the animate-spin. If both are set at the same time
        -- it will rotate as it shrinks.
        liftAff $ waitForAllAnimations buttonElem
        -- NOTE: We manually add the CSS to the DOM element but we never manually remove it.
        --       This is because Halogen will clear it for us when it recomputes the classes
        --       when we call handleQuery.SubmitResult
        classes <- MaybeT $ map pure $ liftEffect $ classList buttonElem
        liftEffect $ DOMTokenList.add classes "animate-spin"
  raise OnSubmit

handleAction (OnNewInput { enabled, styles, caption }) =
  modify_
    $ set _enabled enabled
    <<< set _styles styles
    <<< set _caption caption

handleQuery ::
  forall slots a m.
  MonadAff m =>
  Query a ->
  HalogenM State Action slots Message m (Maybe a)
handleQuery (SubmitResult timeout result next) =
  runMaybeT do
    assign _status $ fromEither result
    buttonHeight <- use _buttonHeight
    buttonElem <- MaybeT $ getHTMLElementRef buttonRef
    let
      styleStr = "height: " <> roundShow buttonHeight <> "px"
    -- We keep the original height for the Result message, but
    -- we remove the width (so that is no longer a circle)
    liftEffect $ setAttribute "style" styleStr $ toElement buttonElem
    -- We pause the execution of this "thread/handler" so we give enough
    -- time for the user to see the result before continuing. Because of
    -- how Halogen works, it will pause the execution of the handleAction
    -- that makes this query without affecting other handleActions
    liftAff $ Aff.delay timeout
    assign _status NotAsked
    liftEffect $ removeAttribute "style" $ toElement buttonElem
    lift $ raise OnResultAnimationFinish
    MaybeT $ pure $ Just next
