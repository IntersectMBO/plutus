module Gists.View
  ( gistControls
  , idPublishGist
  , idLoadGist
  ) where

import Gists.Types (GistAction(..), parseGistUrl)
import AjaxUtils (ajaxErrorPane)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnBlock, btnDanger, btnInfo, btnPrimary, btnSmall, col12_, col6_, empty, formControl, isInvalid, isValid, nbsp, pullRight, row_)
import DOM.HTML.Indexed.InputType (InputType(..))
import Data.Either (Either(..), isRight, note)
import Data.Lens (view)
import Data.Maybe (Maybe(..), fromMaybe)
import Gist (Gist, GistId, gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, IProp, a, button, div, div_, input, text)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, href, id_, placeholder, target, type_, value)
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
  , gistUrl :: Maybe String
  | a
  } ->
  HTML p GistAction
gistControls { authStatus, createGistResult, gistUrl } =
  div
    [ class_ $ ClassName "gist-controls" ]
    [ authButton
        $ div_
            [ div
                [ class_ $ ClassName "form-inline" ]
                [ input
                    [ type_ InputText
                    , value $ fromMaybe "" $ gistUrl
                    , id_ "gist-id"
                    , classes
                        ( [ formControl, ClassName "form-control-sm" ]
                            <> case parsedGistId of
                                Just (Left err) -> [ isInvalid ]
                                Just (Right err) -> [ isValid ]
                                Nothing -> []
                        )
                    , placeholder "Load Gist ID"
                    , onValueInput $ Just <<< SetGistUrl
                    ]
                , publishButton
                , loadButton
                ]
            , case createGistResult of
                Success gist -> gistPane gist
                Failure err -> ajaxErrorPane err
                Loading -> empty
                NotAsked -> empty
            ]
    ]
  where
  canTryLoad = isRight $ parseGistUrl =<< note "No gist Url set" gistUrl

  parsedGistId :: Maybe (Either String GistId)
  parsedGistId = parseGistUrl <$> gistUrl

  authButton authorisedView = case view authStatusAuthRole <$> authStatus of
    Failure _ ->
      button
        [ idPublishGist
        , classes [ btn, btnDanger, pullRight ]
        ]
        [ text "Failure" ]
    Success Anonymous ->
      a
        [ idPublishGist
        , classes [ btn, btnInfo, pullRight ]
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
        , classes [ btn, btnInfo, pullRight ]
        , disabled true
        ]
        [ icon Spinner ]
    NotAsked ->
      button
        [ idPublishGist
        , classes [ btn, btnInfo, pullRight ]
        , disabled true
        ]
        [ icon Spinner ]

  publishButton = case createGistResult of
    Failure _ ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnDanger ]
        ]
        [ text "Failure" ]
    Success _ ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnPrimary ]
        , onClick $ const $ Just PublishGist
        ]
        [ icon Github, nbsp, text "Republish" ]
    Loading ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnInfo ]
        , disabled true
        ]
        [ icon Spinner ]
    NotAsked ->
      button
        [ idPublishGist
        , classes [ btn, btnSmall, btnPrimary ]
        , onClick $ const $ Just PublishGist
        ]
        [ icon Github, nbsp, text "Publish" ]

  loadMessage = [ icon Github, nbsp, text "Load" ]

  loadButton = case createGistResult of
    Loading -> empty
    _ ->
      button
        [ idLoadGist
        , classes
            [ btn
            , btnSmall
            , case parsedGistId of
                Just (Left url) -> btnDanger
                Just (Right url) -> btnPrimary
                Nothing -> btnInfo
            ]
        , onClick $ const $ Just LoadGist
        , disabled
            $ case parsedGistId of
                Just (Left url) -> true
                Just (Right url) -> false
                Nothing -> true
        ]
        loadMessage

gistPane :: forall p i. Gist -> HTML p i
gistPane gist =
  div [ class_ $ ClassName "gist-link" ]
    [ a
        [ href $ view gistHtmlUrl gist
        , target "_blank"
        ]
        [ text $ "View on Github" ]
    ]
