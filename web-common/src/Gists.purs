module Gists
  ( GistAction(..)
  , gistControls
  , parseGistUrl
  , idPublishGist
  , idLoadGist
  ) where

import AjaxUtils (ajaxErrorPane)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnBlock, btnDanger, btnInfo, btnPrimary, btnSmall, col12_, col6_, empty, formControl, isInvalid, isValid, nbsp, pullRight, row_)
import DOM.HTML.Indexed.InputType (InputType(..))
import Data.Array.NonEmpty as NonEmptyArray
import Data.Either (Either(..), isRight, note)
import Data.Lens (findOf, traversed, view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String.Regex (Regex, match, regex)
import Data.String.Regex.Flags (ignoreCase)
import Gist (Gist, GistFile, GistId(GistId), gistFileFilename, gistFiles, gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, IProp, a, button, div, div_, input, text)
import Halogen.HTML.Events (onClick, onValueInput)
import Halogen.HTML.Properties (class_, classes, disabled, href, id_, placeholder, target, type_, value)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Prelude (bind, const, ($), (<$>), (<<<), (<>), (=<<), (==))
import Servant.PureScript.Ajax (AjaxError)

idPublishGist :: forall r i. IProp ( id :: String | r ) i
idPublishGist = id_ "publish-gist"

idLoadGist :: forall r i. IProp ( id :: String | r ) i
idLoadGist = id_ "load-gist"

data GistAction
  = PublishGist
  | SetGistUrl String
  | LoadGist

gistControls ::
  forall a p.
  { authStatus :: RemoteData AjaxError AuthStatus
  , createGistResult :: RemoteData AjaxError Gist
  , gistUrl :: Maybe String
  | a
  } ->
  HTML p GistAction
gistControls { authStatus, createGistResult, gistUrl } =
  div [ classes [ ClassName "gist-controls" ] ]
    [ authButton
        $ div_
            [ row_
                [ col12_
                    [ input
                        [ type_ InputText
                        , value $ fromMaybe "" $ gistUrl
                        , id_ "gist-id"
                        , classes
                            ( [ formControl ]
                                <> case parsedGistId of
                                    Just (Left err) -> [ isInvalid ]
                                    Just (Right err) -> [ isValid ]
                                    Nothing -> []
                            )
                        , placeholder "Load Gist ID"
                        , onValueInput $ Just <<< SetGistUrl
                        ]
                    ]
                , col6_ [ publishButton ]
                , col6_ [ loadButton ]
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
        , classes [ btn, btnBlock, btnSmall, btnDanger ]
        ]
        [ text "Failure" ]
    Success _ ->
      button
        [ idPublishGist
        , classes [ btn, btnBlock, btnSmall, btnPrimary ]
        , onClick $ const $ Just PublishGist
        ]
        [ icon Github, nbsp, text "Republish" ]
    Loading ->
      button
        [ idPublishGist
        , classes [ btn, btnBlock, btnSmall, btnInfo ]
        , disabled true
        ]
        [ icon Spinner ]
    NotAsked ->
      button
        [ idPublishGist
        , classes [ btn, btnBlock, btnSmall, btnPrimary ]
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
            , btnBlock
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

gistIdInLinkRegex :: Either String Regex
gistIdInLinkRegex = regex "^(.*/)?([0-9a-f]{32})$" ignoreCase

parseGistUrl :: String -> Either String GistId
parseGistUrl str = do
  gistIdInLink <- gistIdInLinkRegex
  note "Could not parse Gist Url"
    $ do
        matches <- match gistIdInLink str
        match <- NonEmptyArray.index matches 2
        GistId <$> match