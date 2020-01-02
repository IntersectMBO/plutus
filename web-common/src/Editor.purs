module Editor
  ( EditorAction(..)
  , editorPane
  , compileButton
  , initEditor
  , withEditor
  ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage, AceQuery(..), Autocomplete(Live), aceComponent)
import Ace.Types (Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnPrimary, btnSecondary, btnSuccess, empty, listGroupItem_, listGroup_, pullRight)
import Control.Alternative ((<|>))
import Data.Either (Either(..))
import Data.Lens (Lens', _Right, preview, to, view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String as String
import Data.Symbol (class IsSymbol, SProxy(..))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, Slot, liftEffect, query, request)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, br_, button, code_, div, div_, h3_, pre_, slot, small, text)
import Halogen.HTML.Events (onClick, onDragOver, onDrop)
import Halogen.HTML.Properties (class_, classes, disabled, id_)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), Warning, _Warning, InterpreterResult, _InterpreterResult)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Prelude (class Ord, Unit, bind, const, discard, join, map, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import Prim.Row as Row
import Servant.PureScript.Ajax (AjaxError)
import Web.HTML.Event.DragEvent (DragEvent)

data EditorAction
  = HandleEditorMessage AceMessage
  | HandleDragEvent DragEvent
  | HandleDropEvent DragEvent
  | LoadScript String
  | ScrollTo { row :: Int, column :: Int }
  | CompileProgram

_warnings :: forall s a. Lens' { warnings :: a | s } a
_warnings = prop (SProxy :: SProxy "warnings")

initEditor ∷
  forall m.
  MonadAff m =>
  Maybe String -> LocalStorage.Key -> Editor -> m Unit
initEditor initialContents bufferLocalStorageKey editor =
  liftEffect
    $ do
        savedContents <- liftEffect $ LocalStorage.getItem bufferLocalStorageKey
        let
          contents = fromMaybe "" (savedContents <|> initialContents)
        void $ Editor.setValue contents (Just 1) editor
        Editor.setTheme "ace/theme/monokai" editor
        Editor.setShowPrintMargin false editor
        --
        session <- Editor.getSession editor
        Session.setMode "ace/mode/haskell" session

type CompilationState a
  = RemoteData AjaxError (Either InterpreterError (InterpreterResult a))

editorPane ::
  forall m label _1 slots a.
  Row.Cons label (Slot AceQuery AceMessage Unit) _1 slots =>
  IsSymbol label =>
  MonadAff m =>
  Maybe String ->
  SProxy label ->
  LocalStorage.Key ->
  CompilationState a ->
  ComponentHTML EditorAction slots m
editorPane initialContents slotLabel bufferLocalStorageKey state =
  div_
    [ div
        [ id_ "editor"
        , onDragOver $ Just <<< HandleDragEvent
        , onDrop $ Just <<< HandleDropEvent
        ]
        [ slot
            slotLabel
            unit
            (aceComponent (initEditor initialContents bufferLocalStorageKey) (Just Live))
            unit
            (Just <<< HandleEditorMessage)
        ]
    , br_
    , compileButton state
    , br_
    , errorList
    , warningList
    ]
  where
  errorList = case state of
    Success (Left error) -> listGroup_ (interpreterErrorPane error)
    Failure error -> ajaxErrorPane error
    _ -> empty

  warningList =
    fromMaybe empty
      $ preview
          ( _Success
              <<< _Right
              <<< _InterpreterResult
              <<< _warnings
              <<< to compilationWarningsPane
          )
          state

compileButton :: forall p a. CompilationState a -> HTML p EditorAction
compileButton state =
  button
    [ id_ "compile"
    , classes [ btn, btnClass ]
    , onClick $ const $ Just $ CompileProgram
    , disabled (isLoading state)
    ]
    [ btnText ]
  where
  btnClass = case state of
    Success (Right _) -> btnSuccess
    Success (Left _) -> btnDanger
    Failure _ -> btnDanger
    Loading -> btnSecondary
    NotAsked -> btnPrimary

  btnText = case state of
    Loading -> icon Spinner
    _ -> text "Compile"

interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p EditorAction)
interpreterErrorPane (TimeoutError error) = [ listGroupItem_ [ div_ [ text error ] ] ]

interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

compilationErrorPane :: forall p. CompilationError -> HTML p EditorAction
compilationErrorPane (RawError error) = div_ [ text error ]

compilationErrorPane (CompilationError error) =
  div
    [ class_ $ ClassName "compilation-error"
    , onClick $ const $ Just $ ScrollTo { row: error.row, column: error.column }
    ]
    [ small [ class_ pullRight ] [ text "jump" ]
    , h3_ [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":" ]
    , code_ [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]

compilationWarningsPane :: forall p. Array Warning -> HTML p EditorAction
compilationWarningsPane warnings = listGroup_ (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

compilationWarningPane :: forall p. Warning -> HTML p EditorAction
compilationWarningPane warning = div [ class_ $ ClassName "compilation-warning" ] [ text $ view _Warning warning ]

-- | Handles the messy business of running an editor command if the
-- editor is up and running.
withEditor ::
  forall label slotIndex _1 state action slots output m a.
  Row.Cons label (Slot AceQuery AceMessage slotIndex) _1 slots =>
  Ord slotIndex =>
  MonadEffect m =>
  IsSymbol label =>
  SProxy label ->
  slotIndex ->
  (Editor -> Effect a) ->
  HalogenM state action slots output m (Maybe a)
withEditor label slotIndex action = do
  mEditor <- query label slotIndex $ request GetEditor
  case join mEditor of
    Just editor -> Just <$> (liftEffect $ action editor)
    _ -> pure Nothing
