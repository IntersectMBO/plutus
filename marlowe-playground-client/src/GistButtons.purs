module GistButtons (authButton) where

import Prelude hiding (div)
import Auth (AuthRole(..), authStatusAuthRole)
import Data.Lens (to, view, (^.))
import Data.Maybe (Maybe(..))
import Gists.View (idPublishGist)
import Halogen.Classes (modalContent)
import Halogen.HTML (ClassName(..), HTML, a, button, div, div_, p_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, disabled)
import Icons (Icon(..), icon)
import MainFrame.Types (Action(..), State, _authStatus)
import Modal.ViewHelpers (modalHeader)
import Network.RemoteData (RemoteData(..))
import Prim.TypeError (class Warn, Text)

authButton ::
  forall p.
  Warn (Text "We need to redesign the authButton modal after this task is done SCP-1512") =>
  Action ->
  State ->
  HTML p Action
authButton intendedAction state =
  let
    authStatus = state ^. (_authStatus <<< to (map (view authStatusAuthRole)))
  in
    case authStatus of
      Failure _ ->
        button
          [ idPublishGist
          ]
          [ text "Failed to login" ]
      Success Anonymous ->
        div_
          [ modalHeader "Login with github" (Just CloseModal)
          , div [ classes [ modalContent, ClassName "auth-button-container" ] ]
              [ p_ [ text "We use gists to save your projects, in order to save and load your projects you will need to login to Github." ]
              , p_ [ text "If you don't wish to login you can still use the Marlowe Playground however you won't be able to save your work." ]
              , div_
                  [ a
                      [ idPublishGist
                      , classes [ ClassName "auth-button" ]
                      , onClick $ const $ Just $ OpenLoginPopup intendedAction
                      ]
                      [ text "Login"
                      ]
                  ]
              ]
          ]
      Success GithubUser -> text ""
      Loading ->
        button
          [ idPublishGist
          , disabled true
          ]
          [ icon Spinner ]
      NotAsked ->
        button
          [ idPublishGist
          , disabled true
          ]
          [ icon Spinner ]
