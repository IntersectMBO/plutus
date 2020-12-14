module Projects.State where

import Prelude hiding (div)
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
import Halogen.Classes (fontSemibold, modalContent, textSm)
import Halogen.HTML (HTML, a, a_, div, div_, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Marlowe (SPParams_, getApiGists)
import Marlowe.Gists (fileExists, filenames, playgroundGist)
import Modal.ViewHelpers (modalHeaderTitle)
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
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
    , div [ classes [ modalContent ] ]
        [ body (view _projects state)
        ]
    ]
  where
  body (Success []) = span [ class_ (ClassName "empty-result") ] [ text "No saved projects found" ]

  body (Success gists) = projectList $ filter playgroundGist gists

  body (Failure _) = span [ class_ (ClassName "error") ] [ text "Failed to load gists" ]

  body Loading = span [ class_ (ClassName "loading") ] [ text "Loading..." ]

  body NotAsked = text mempty

projectList ::
  forall p.
  Array Gist ->
  HTML p Action
projectList gists =
  div [ classes [ ClassName "project-list" ] ]
    (headers <> projects)
  where
  headers :: Array (HTML p Action)
  headers =
    [ "Name", "Created", "Last Updated", "Open" ]
      <#> \name ->
          div [ classes [ textSm, fontSemibold ] ] [ text name ]

  -- FIXME: Only 30 projects seem to be loading. Check why and define what should we do about it
  projects :: Array (HTML p Action)
  projects =
    gists
      >>= \gist ->
          [ div [ class_ (ClassName "project-name") ] [ gist ^. (gistDescription <<< to text) ]
          , div [ class_ (ClassName "date") ] [ gist ^. (gistCreatedAt <<< to formatDate <<< to text) ]
          , div [ class_ (ClassName "date") ] [ gist ^. (gistUpdatedAt <<< to formatDate <<< to text) ]
          , loadLink gist Javascript "Javascript" $ fileExists filenames.javascript gist
          , loadLink gist Haskell "Haskell" $ fileExists filenames.haskell gist
          , loadLink gist Marlowe "Marlowe" $ fileExists filenames.marlowe gist
          , loadLink gist Blockly "Blockly" $ fileExists filenames.blockly gist
          ]

  loadLink :: Gist -> Lang -> String -> Boolean -> HTML p Action
  loadLink gist action name = case _ of
    false -> div [ classes [ ClassName "language-link", ClassName "disabled" ] ] $ [ a_ $ [ text name ] ]
    true -> div [ classes [ ClassName "language-link" ] ] $ [ a [ onClick (const <<< Just $ LoadProject action (gist ^. gistId)) ] $ [ text name ] ]

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
