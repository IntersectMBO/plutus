module Gists
       ( gistControls
       , mkNewGist
       , gistSourceFilename
       , gistSimulationFilename
       , parseGistUrl
       , playgroundGistFile
       , simulationGistFile
       )
       where

import AjaxUtils (getEncodeJson, showAjaxError)
import Auth (AuthRole(..), authStatusAuthRole)
import Bootstrap (btn, btnBlock, btnDanger, btnInfo, btnPrimary, empty, formControl, isInvalid, isValid, nbsp)
import Control.Monad.Reader.Trans (class MonadAsk)
import Cursor (Cursor)
import DOM.HTML.Indexed.InputType (InputType(..))
import Data.Argonaut.Core (stringify)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Either (Either(..), isRight, note)
import Data.Lens (findOf, traversed, view)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String.Regex (Regex, match, regex)
import Data.String.Regex.Flags (ignoreCase)
import Gist (Gist, GistFile, GistId(GistId), NewGist(NewGist), NewGistFile(NewGistFile), gistFileFilename, gistFiles, gistHtmlUrl)
import Halogen.HTML (ClassName(ClassName), HTML, IProp, a, br_, button, div, div_, input, text)
import Halogen.HTML.Events (input_, onClick, onValueInput)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (class_, classes, disabled, href, id_, placeholder, target, type_, value)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Playground.API (SourceCode)
import Prelude (Unit, bind, pure, ($), (<$>), (<<<), (<>), (=<<), (==))
import Servant.PureScript.Settings (SPSettings_)
import Types (Query(SetGistUrl, LoadGist, PublishGist), Simulation, State(State))

idPublishGist :: forall r i. IProp (id :: String | r) i
idPublishGist = id_ "publish-gist"

idLoadGist :: forall r i. IProp (id :: String | r) i
idLoadGist = id_ "load-gist"

gistControls :: forall p. State -> HTML p (Query Unit)
gistControls (State {authStatus, createGistResult, gistUrl}) =
  div
    [ classes [ ClassName "gist-controls"
              ]
    ]
    [ authButton $
        div_ [ input [ type_ InputText
                     , value $ fromMaybe "" $ gistUrl
                     , classes
                         ( [ formControl ]
                           <>
                           case parsedGistId of
                             Just (Left err) -> [ isInvalid ]
                             Just (Right err) -> [ isValid ]
                             Nothing -> []
                         )
                     , placeholder "Paste in a Gist link"
                     , onValueInput $ HE.input SetGistUrl
                     ]
             , br_
             , loadButton
             , publishButton
             , div_
                 [ case createGistResult of
                      Success gist -> gistPane gist
                      Failure err -> showAjaxError err
                      Loading -> nbsp
                      NotAsked -> nbsp
                 ]
             ]
    ]
  where
    canTryLoad = isRight $ parseGistUrl =<< note "No gist Url set" gistUrl

    parsedGistId :: Maybe (Either String GistId)
    parsedGistId = parseGistUrl <$> gistUrl

    authButton authorisedView =
      case view authStatusAuthRole <$> authStatus of
        Failure _ ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnDanger ]
            ]
            [ text "Failure" ]
        Success Anonymous ->
          a
            [ idPublishGist
            , classes [ btn, btnBlock, btnInfo ]
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
            , classes [ btn, btnBlock, btnInfo ]
            , disabled true
            ]
            [ icon Spinner ]
        NotAsked ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnInfo ]
            , disabled true
            ]
            [ icon Spinner ]

    publishButton =
      case createGistResult of
        Failure _ ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnDanger ]
            ]
            [ text "Failure" ]
        Success _ ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnPrimary ]
            , onClick $ input_ PublishGist
            ]
            [ icon Github, nbsp, text "Republish" ]
        Loading ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnInfo ]
            , disabled true
            ]
            [ icon Spinner ]
        NotAsked ->
          button
            [ idPublishGist
            , classes [ btn, btnBlock, btnPrimary ]
            , onClick $ input_ PublishGist
            ]
            [ icon Github, nbsp, text "Publish" ]

    loadMessage = [ icon Github, nbsp, text "Load" ]

    loadButton =
      case createGistResult of
        Loading -> empty
        _ ->
          button
            [ idLoadGist
            , classes [ btn
                      , btnBlock
                      , case parsedGistId of
                          Just (Left url) -> btnDanger
                          Just (Right url) ->  btnPrimary
                          Nothing -> btnInfo
                      ]
            , onClick $ input_ LoadGist
            , disabled $ case parsedGistId of
                           Just (Left url) -> true
                           Just (Right url) -> false
                           Nothing -> true
            ]
            loadMessage

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
  forall m params.
  MonadAsk (SPSettings_ params) m
  => { source :: Maybe SourceCode
     , simulations :: Cursor Simulation
     }
  -> m (Maybe NewGist)
mkNewGist  { source, simulations } = do
  encodeJson <- getEncodeJson
  let gistFiles = catMaybes [ mkNewGistFile gistSourceFilename <<< unwrap <$> source
                            , Just (mkNewGistFile gistSimulationFilename $ stringify $ encodeJson simulations)
                            ]
  pure $ if Array.null gistFiles
    then Nothing
    else Just $ NewGist { _newGistDescription: "Plutus Playground Smart Contract"
                        , _newGistPublic: true
                        , _newGistFiles: gistFiles
                        }
  where
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

firstMatch :: String -> Gist -> Maybe GistFile
firstMatch filename = findOf (gistFiles <<< traversed) (\gistFile -> view gistFileFilename gistFile == filename)

playgroundGistFile :: Gist -> Maybe GistFile
playgroundGistFile = firstMatch gistSourceFilename

simulationGistFile :: Gist -> Maybe GistFile
simulationGistFile = firstMatch gistSimulationFilename
