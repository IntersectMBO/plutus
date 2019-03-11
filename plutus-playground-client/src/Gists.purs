module Gists
       ( gistControls
       , mkNewGist
       , gistSourceFilename
       , gistSimulationFilename
       , parseGistUrl
       )
       where

import AjaxUtils (showAjaxError)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnBlock, btnDanger, btnInfo, btnPrimary, btnSecondary, nbsp)
import DOM.HTML.Indexed.InputType (InputType(..))
import Data.Argonaut.Core (stringify)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Either (Either, isRight, note)
import Data.Lens (view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String.Regex (Regex, match, regex)
import Data.String.Regex.Flags (ignoreCase)
import Gist (Gist, GistId(..), NewGist(NewGist), NewGistFile(NewGistFile), gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, a, br_, button, div, div_, input, text)
import Halogen.HTML.Events (input_, onClick, onValueInput)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (class_, classes, disabled, href, id_, placeholder, target, type_, value)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Playground.API (SourceCode)
import Prelude (Unit, bind, not, ($), (<$>), (<<<), (<>), (=<<))
import Servant.PureScript.Affjax (AjaxError)
import Servant.PureScript.Settings (SPSettingsEncodeJson_(..), SPSettings_(..))
import Types (Query(..), Simulation)

gistControls ::
  forall p.
  RemoteData AjaxError AuthStatus
  -> RemoteData AjaxError Gist
  -> Maybe String
  -> HTML p (Query Unit)
gistControls authStatus createGistResult gistUrl =
  div [ class_ $ ClassName "gist-controls" ]
    [ a ([ id_ "publish-gist" ] <> publishAttributes)
        publishContent
    , br_
    , div_
        [ case createGistResult of
             Success gist -> gistPane gist
             Failure err -> showAjaxError err
             Loading -> nbsp
             NotAsked -> nbsp
        ]
    , button
        [ classes ([ btn, btnBlock ] <> if canTryLoad then [ btnPrimary ] else [ btnSecondary ])
        , onClick $ input_ $ LoadGist
        , disabled (not canTryLoad)
        ]
        [ icon Github
        , nbsp
        , text "Load"
        ]
    , input [ type_ InputText
            , value $ fromMaybe "" $ gistUrl
            , placeholder "Paste in a Gist link"
            , onValueInput $ HE.input SetGistUrl
            ]
    ]
  where
    canTryLoad = isRight $ parseGistUrl =<< note "No gist Url set" gistUrl

    publishAttributes =
      case (view authStatusAuthRole <$> authStatus), createGistResult of
        Failure _, _ ->
          [ classes [ btn, btnBlock, btnDanger ] ]
        _, Failure _ ->
          [ classes [ btn, btnBlock, btnDanger ] ]
        Success Anonymous, _ ->
          [ classes [ btn, btnBlock, btnInfo ]
          , href "/api/oauth/github"
          ]
        Success GithubUser, NotAsked ->
          [ classes [ btn, btnBlock, btnPrimary ]
          , onClick $ input_ PublishGist
          ]
        Success GithubUser, Success _ ->
          [ classes [ btn, btnBlock, btnPrimary ]
          , onClick $ input_ PublishGist
          ]
        Loading, _ ->
          [ classes [ btn, btnBlock, btnInfo ] ]
        _, Loading ->
          [ classes [ btn, btnBlock, btnInfo ] ]
        NotAsked, _ ->
          [ classes [ btn, btnBlock, btnInfo ] ]

    publishContent =
      case (view authStatusAuthRole <$> authStatus), createGistResult of
        Failure _, _ ->
          [ text "Failure" ]
        _, Failure _ ->
          [ text "Failure" ]
        Success Anonymous, _ ->
          [ icon Github, nbsp, text "Publish" ]
        Success GithubUser, NotAsked ->
          [ icon Github, nbsp, text "Publish" ]
        Success GithubUser, Success _ ->
          [ icon Github, nbsp, text "Republish" ]
        Loading, _ ->
          [ icon Spinner ]
        _, Loading ->
          [ icon Spinner ]
        NotAsked, _ ->
          [ icon Github, nbsp, text "Publish" ]

gistPane :: forall p i. Gist -> HTML p i
gistPane gist =
  div
    [ class_ $ ClassName "gist-link" ]
    [ a
        [ href $ view gistHtmlUrl gist
        , target "_blank"
        ]
      [ text $ "View on Github" ]
    ]

mkNewGist ::
  forall params.
  SPSettings_ params ->
  { source :: Maybe SourceCode
  , simulation :: Maybe Simulation
  }
  -> Maybe NewGist
mkNewGist (SPSettings_ {encodeJson: (SPSettingsEncodeJson_ encodeJson)}) { source, simulation } =
  if Array.null gistFiles
  then Nothing
  else Just $ NewGist { _newGistDescription: "Plutus Playground Smart Contract"
                      , _newGistPublic: true
                      , _newGistFiles: gistFiles
                      }
    where
      gistFiles =
        catMaybes [ mkNewGistFile gistSourceFilename <<< unwrap <$> source
                  , mkNewGistFile gistSimulationFilename <<< stringify <<< encodeJson <$> simulation
                  ]

      mkNewGistFile _newGistFilename _newGistFileContent =
        NewGistFile { _newGistFilename
                    , _newGistFileContent
                    }

gistSourceFilename :: String
gistSourceFilename = "Playground.hs"

gistSimulationFilename :: String
gistSimulationFilename = "Simulation.json"

gistIdInLinkRegex :: Either String Regex
gistIdInLinkRegex = regex "^(.*/)?([0-9a-f]{32})$" ignoreCase

parseGistUrl :: String -> Either String GistId
parseGistUrl str = do
  gistIdInLink <- gistIdInLinkRegex
  note "Could not parse Gist Url" $ do matches <- match gistIdInLink str
                                       match <- Array.index matches 2
                                       GistId <$> match
