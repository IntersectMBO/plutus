module Gists
       ( gistControls
       , mkNewGist
       )
       where

import AjaxUtils (showAjaxError)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnDanger, btnInfo, btnPrimary, nbsp)
import Data.Argonaut.Core (stringify)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Gist (Gist, NewGist(NewGist), NewGistFile(NewGistFile), gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, a, br_, div, div_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (class_, classes, href, id_, target)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Playground.API (Evaluation, SourceCode)
import Prelude (Unit, join, ($), (<$>), (<*>), (<<<), (<>))
import Servant.PureScript.Affjax (AjaxError)
import Servant.PureScript.Settings (SPSettingsEncodeJson_(..), SPSettings_(..))
import Types (Query(PublishGist), Simulation, toEvaluation)

gistControls ::
  forall p.
  RemoteData AjaxError AuthStatus
  -> RemoteData AjaxError Gist
  -> HTML p (Query Unit)
gistControls authStatus createGistResult =
  div_
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
    ]
  where

    publishAttributes =
      case (view authStatusAuthRole <$> authStatus), createGistResult of
        Failure _, _ ->
          [ classes [ btn, btnDanger ] ]
        _, Failure _ ->
          [ classes [ btn, btnDanger ] ]
        Success Anonymous, _ ->
          [ classes [ btn, btnInfo ]
          , href "/api/oauth/github"
          ]
        Success GithubUser, NotAsked ->
          [ classes [ btn, btnPrimary ]
          , onClick $ input_ PublishGist
          ]
        Success GithubUser, Success _ ->
          [ classes [ btn, btnPrimary ]
          , onClick $ input_ PublishGist
          ]
        Loading, _ ->
          [ classes [ btn, btnInfo ] ]
        _, Loading ->
          [ classes [ btn, btnInfo ] ]
        NotAsked, _ ->
          [ classes [ btn, btnInfo ] ]

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
      evaluation :: Maybe Evaluation
      evaluation = join $ toEvaluation <$> source <*> simulation

      gistFiles =
        catMaybes [ mkNewGistFile "Playground.hs" <<< unwrap <$> source
                  , mkNewGistFile "Simulation.json" <<< stringify <<< encodeJson <$> evaluation
                  ]

      mkNewGistFile _newGistFilename _newGistFileContent =
        NewGistFile { _newGistFilename
                    , _newGistFileContent
                    }
