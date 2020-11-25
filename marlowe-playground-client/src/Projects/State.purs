module Projects.State where

import Control.Monad.Except (runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (filter, sortBy)
import Data.Bifunctor (lmap, rmap)
import Data.DateTime (DateTime)
import Data.DateTime.ISO as ISO
import Data.Either (Either(..), hush)
import Data.Formatter.DateTime (FormatterCommand(..), format)
import Data.Lens (assign, to, view, (^.))
import Data.List (fromFoldable)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Ordering (invert)
import Effect.Aff.Class (class MonadAff)
import Gist (Gist(..), gistCreatedAt, gistDescription, gistId, gistUpdatedAt)
import Halogen (ClassName(..), ComponentHTML, HalogenM)
import Halogen.Classes (flex, modalContent)
import Halogen.HTML (HTML, a, div, div_, span, table, tbody, td, td_, text, th_, thead, tr, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_, getApiGists)
import Marlowe.Gists (fileExists, filenames, playgroundGist)
import Modal.ViewHelpers (modalHeaderTitle)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (Unit, Void, bind, bottom, compare, const, discard, flip, map, mempty, pure, unit, ($), (<<<))
import Prim.TypeError (class Warn, Text)
import Projects.Types (Action(..), Lang(..), State, _projects)
import Servant.PureScript.Ajax (errorToString)
import Servant.PureScript.Settings (SPSettings_)
import Text.Parsing.Parser (runParser)

handleAction ::
  forall m.
  MonadAff m =>
  SPSettings_ SPParams_ ->
  Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings LoadProjects = do
  assign _projects Loading
  resp <- flip runReaderT settings $ runExceptT getApiGists
  assign _projects $ rmap sortGists $ lmap errorToString $ RemoteData.fromEither resp

handleAction settings (LoadProject lang gistId) = pure unit

sortGists :: Array Gist -> Array Gist
sortGists = sortBy f
  where
  dt :: String -> DateTime
  dt s = fromMaybe bottom <<< map unwrap <<< hush $ runParser s ISO.parseISO

  f (Gist { _gistUpdatedAt: a }) (Gist { _gistUpdatedAt: b }) = invert $ compare (dt a) (dt b)

render ::
  forall m.
  Warn (Text "Fix 'body Loading' design") =>
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ modalHeaderTitle "Open Project"
    , div [ classes [ modalContent, ClassName "projects-container" ] ]
        [ body (view _projects state)
        ]
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
            , th_ [ text "Last Updated" ]
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
    , td [ class_ (ClassName "date") ] [ gist ^. (gistUpdatedAt <<< to formatDate <<< to text) ]
    , td_
        [ div [ classes [ flex, ClassName "language-links" ] ]
            [ loadLink Haskell "Haskell" $ fileExists filenames.haskell gist
            , loadLink Javascript "Javascript" $ fileExists filenames.javascript gist
            , loadLink Marlowe "Marlowe" $ fileExists filenames.marlowe gist
            , loadLink Blockly "Blockly" $ fileExists filenames.blockly gist
            ]
        ]
    ]
  where
  loadLink :: Lang -> String -> Boolean -> HTML p Action
  loadLink _ _ false = div [ class_ (ClassName "empty") ] []

  loadLink action name _ = a [ onClick (const <<< Just $ LoadProject action (gist ^. gistId)) ] [ text name ]
