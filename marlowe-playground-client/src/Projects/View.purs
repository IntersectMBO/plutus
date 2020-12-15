module Projects.View (render) where

import Prelude hiding (div)
import Data.Array (filter)
import Data.DateTime.ISO as ISO
import Data.Either (Either(..))
import Data.Formatter.DateTime (FormatterCommand(..), format)
import Data.Lens (to, view, (^.))
import Data.List (fromFoldable)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Effect.Aff.Class (class MonadAff)
import Gist (Gist, gistCreatedAt, gistDescription, gistId, gistUpdatedAt)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (fontSemibold, modalContent, textSm)
import Halogen.HTML (HTML, a, a_, div, div_, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Marlowe.Gists (fileExists, filenames, playgroundGist)
import Modal.ViewHelpers (modalHeaderWithClose)
import Network.RemoteData (RemoteData(..))
import Prim.TypeError (class Warn, Text)
import Projects.Types (Action(..), Lang(..), State, _projects)
import Text.Parsing.Parser (runParser)

render ::
  forall m.
  Warn (Text "Fix 'body Loading' design") =>
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ modalHeaderWithClose "Open Project" Cancel
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
  Warn (Text "Only 30 projects seem to be loading. Check why and define what should we do about it") =>
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
