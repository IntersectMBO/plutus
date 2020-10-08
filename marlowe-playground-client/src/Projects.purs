module Projects where

import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (filter)
import Data.Bifunctor (lmap)
import Data.DateTime.ISO as ISO
import Data.Either (Either(..))
import Data.Formatter.DateTime (FormatterCommand(..), format)
import Data.Lens (assign, to, view, (^.))
import Data.List (fromFoldable)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect.Aff.Class (class MonadAff)
import Gist (Gist, gistCreatedAt, gistDescription, gistId)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (flex)
import Halogen.HTML (HTML, a, div, h1_, hr_, span, table, tbody, td, td_, text, th_, thead, tr, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Marlowe (SPParams_, getApiGists)
import Marlowe.Gists (playgroundGist)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, const, discard, flip, map, mempty, pure, unit, ($), (<<<))
import Projects.Types (Action(..), Lang(..), State, _projects)
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Text.Parsing.Parser (runParser)
import Types (ChildSlots)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings LoadProjects = do
  assign _projects Loading
  resp <- flip runReaderT settings $ runExceptT getApiGists
  assign _projects $ lmap errorToString $ RemoteData.fromEither resp

handleAction settings (LoadProject lang gistId) = pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ ClassName "projects-container" ] ]
    [ h1_ [ text "Open Project" ]
    , hr_
    , body (view _projects state)
    ]
  where
  body (Success []) = span [ class_ (ClassName "empty-result") ] [ text "No saved projects found" ]

  body (Success gists) = gistsTable $ filter playgroundGist gists

  body (Failure _) = span [ class_ (ClassName "error") ] [ text "Failed to load gists" ]

  body Loading = span [ class_ (ClassName "loading") ] [ text "Loading..." ]

  body NotAsked = text mempty

gistsTable ::
  forall p.
  Array Gist ->
  HTML p Action
gistsTable gists =
  table [ classes [ ClassName "gists" ] ]
    [ thead []
        [ tr_
            [ th_ [ text "Name" ]
            , th_ [ text "Created" ]
            , th_ [ text "Open" ]
            ]
        ]
    , tbody [] (map gistRow gists)
    ]

formatDate :: String -> String
formatDate s = case runParser s ISO.parseISO of
  Left err -> "Unknown Date"
  Right iso ->
    format
      ( fromFoldable
          [ DayOfMonth
          , Placeholder "/"
          , MonthTwoDigits
          , Placeholder "/"
          , YearFull
          , Placeholder " "
          , Hours24
          , Placeholder ":"
          , MinutesTwoDigits
          ]
      )
      (unwrap iso)

gistRow ::
  forall p.
  Gist ->
  HTML p Action
gistRow gist =
  tr []
    [ td_ [ gist ^. (gistDescription <<< to text) ]
    , td [ class_ (ClassName "date") ] [ gist ^. (gistCreatedAt <<< to formatDate <<< to text) ]
    , td_
        [ div [ classes [ flex, ClassName "language-links" ] ]
            [ a [ onClick (const <<< Just $ LoadProject Haskell (gist ^. gistId)) ] [ text "Haskell" ]
            , a [ onClick (const <<< Just $ LoadProject Marlowe (gist ^. gistId)) ] [ text "Marlowe" ]
            , a [ onClick (const <<< Just $ LoadProject Blockly (gist ^. gistId)) ] [ text "Blockly" ]
            ]
        ]
    ]
