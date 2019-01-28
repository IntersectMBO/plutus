module Gists
       ( gistControls
       , mkNewGist
       )
       where

import AjaxUtils (showAjaxError)
import Auth (AuthRole(..), AuthStatus, authStatusAuthRole)
import Bootstrap (btn, btnInfo, nbsp)
import Data.Array (catMaybes)
import Data.Array as Array
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Gist (Gist, NewGist(..), NewGistFile(..), _GistId, gistHtmlUrl, gistId)
import Halogen.HTML (HTML, a, button, div_, i_, text)
import Halogen.HTML.Events (input_, onClick)
import Halogen.HTML.Properties (classes, disabled, href, target)
import Network.RemoteData (RemoteData(..), isSuccess)
import Prelude (Unit, not, ($), (<$>), (<<<), (<>))
import Servant.PureScript.Affjax (AjaxError)
import Types (Query(..))

gistControls ::
  forall p.
  RemoteData AjaxError AuthStatus
  -> RemoteData AjaxError Gist
  -> HTML p (Query Unit)
gistControls authStatus createGistResult =
  div_
    [ div_ [ i_ [
               case view authStatusAuthRole <$> authStatus of
                 Success GithubUser -> text "Authenticated with Github."
                 Success Anonymous -> authenticationLink
                 Failure err -> showAjaxError err
                 Loading -> text "Publishing..."
                 NotAsked -> authenticationLink
             ]
           ]
    , button
        [ classes [ btn, btnInfo ]
        , disabled (not (isSuccess authStatus))
        , onClick $ input_ PublishGist
        ]
        [ case createGistResult of
             Success _ -> text "Republish"
             Failure _ -> text "Failure"
             Loading -> text "Loading..."
             NotAsked -> text "Publish"
        ]
    , div_
        [ case createGistResult of
             Success gist -> gistPane gist
             Failure err -> showAjaxError err
             Loading -> nbsp
             NotAsked -> nbsp
        ]
    ]
  where
    authenticationLink = a [ href "/api/oauth/github" ] [ text "Please Authenticate" ]

gistPane :: forall p i. Gist -> HTML p i
gistPane gist =
  div_
    [ a [ href $ view gistHtmlUrl gist
        , target "_blank"
        ]
      [ text $ "Published as: " <> view (gistId <<< _GistId) gist ]
    ]

mkNewGist :: Maybe String -> Maybe NewGist
mkNewGist mSource =
  if Array.null gistFiles
  then Nothing
  else Just $ NewGist { _newGistDescription: "Plutus Playground Smart Contract"
                      , _newGistPublic: true
                      , _newGistFiles: gistFiles
                      }
    where
      gistFiles =
        catMaybes [ mkNewGistFile "Playground.hs" <$> mSource
                  ]

      mkNewGistFile _newGistFilename _newGistFileContent =
        NewGistFile { _newGistFilename
                    , _newGistFileContent
                    }
