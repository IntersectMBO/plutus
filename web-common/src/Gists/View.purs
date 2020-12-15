module Gists.View
  ( gistControls
  , idPublishGist
  , idLoadGist
  ) where

import Gists.Types (GistAction(..), parseGistUrl)
import AjaxUtils (closeableAjaxErrorPane)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnDanger, btnSecondary, btnSmall, empty, formControl, formGroup, isInvalid, isValid, nbsp)
import DOM.HTML.Indexed.InputType (InputType(..))
import Data.Either (Either(..), isRight, note)
import Data.Lens (view)
import Data.Maybe (Maybe(..), fromMaybe)
import Gist (Gist, GistId, gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, IProp, a, button, div, input, label, text)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, for, href, id_, target, type_, value)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Prelude (const, ($), (<$>), (<<<), (<>), (=<<))
import Servant.PureScript.Ajax (AjaxError)

idPublishGist :: forall r i. IProp ( id :: String | r ) i
idPublishGist = id_ "publish-gist"

idLoadGist :: forall r i. IProp ( id :: String | r ) i
idLoadGist = id_ "load-gist"

gistControls ::
  forall a p.
  { authStatus :: RemoteData AjaxError AuthStatus
  , createGistResult :: RemoteData AjaxError Gist
  , gistErrorPaneVisible :: Boolean
  , gistUrl :: Maybe String
  | a
  } ->
  HTML p GistAction
gistControls { authStatus, createGistResult, gistErrorPaneVisible, gistUrl } =
  authButton
    $ div
        [ class_ $ ClassName "gist-controls" ]
        [ div
            [ class_ $ ClassName "form-inline" ]
            [ div
                [ class_ formGroup ]
                [ label
                    [ for gistIdInputId ]
                    [ text "Gist ID" ]
                , input
                    [ type_ InputText
                    , value $ fromMaybe "" $ gistUrl
                    , id_ gistIdInputId
                    , classes
                        ( [ formControl, ClassName "form-control-sm" ]
                            <> case parsedGistId of
                                Just (Left err) -> [ isInvalid ]
                                Just (Right err) -> [ isValid ]
                                Nothing -> []
                        )
                    , onValueInput $ Just <<< SetGistUrl
                    ]
                ]
            , loadButton
            , publishButton
            ]
        , case createGistResult of
            Success gist -> gistPane gist
            Failure err -> AjaxErrorPaneAction <$> closeableAjaxErrorPane err
            Loading -> empty
            NotAsked -> empty
        ]
  where
  gistIdInputId = "gist-id"

  canTryLoad = isRight $ parseGistUrl =<< note "No gist Url set" gistUrl

  parsedGistId :: Maybe (Either String GistId)
  parsedGistId = parseGistUrl <$> gistUrl

  authButton authorisedView = case view authStatusAuthRole <$> authStatus of
    Failure _ ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnDanger ]
        ]
        [ text "Failure" ]
    Success Anonymous ->
      a
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary ]
        , href "/api/oauth/github"
        ]
        [ icon Github
        , nbsp
        , text "Log In"
        ]
    Success GithubUser -> authorisedView
    Loading ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary ]
        , disabled true
        ]
        [ icon Spinner ]
    NotAsked ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary ]
        , disabled true
        ]
        [ icon Spinner ]

  publishButton = case createGistResult of
    Success _ ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary ]
        , onClick $ const $ Just PublishGist
        ]
        [ text "Republish" ]
    Loading ->
      -- make the button extra wide in this case, because there's no load button
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary, ClassName "double-width" ]
        , disabled true
        ]
        [ icon Spinner ]
    _ ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnSecondary ]
        , onClick $ const $ Just PublishGist
        ]
        [ text "Publish" ]

  loadButton = case createGistResult of
    -- no load button in this case; publish button should be twice the size
    Loading -> empty
    _ ->
      button
        [ idLoadGist
        , classes
            [ btn
            , btnSmall
            , case parsedGistId of
                Just (Left url) -> btnDanger
                Just (Right url) -> btnSecondary
                Nothing -> btnSecondary
            ]
        , onClick $ const $ Just LoadGist
        , disabled
            $ case parsedGistId of
                Just (Left url) -> true
                Just (Right url) -> false
                Nothing -> true
        ]
        [ text "Load" ]

gistPane :: forall p i. Gist -> HTML p i
gistPane gist =
  div [ class_ $ ClassName "gist-link" ]
    [ a
        [ href $ view gistHtmlUrl gist
        , target "_blank"
        ]
        [ text $ "View on Github" ]
    ]
