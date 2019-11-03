module Editor
  ( editorPane
  , demoScriptsPane
  , withEditor
  ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceMessage, AceQuery(..), Autocomplete(Live), aceComponent)
import Ace.Types (Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, empty, listGroupItem_, listGroup_, pullRight)
import Control.Alternative ((<|>))
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (_Right, preview, to, view)
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String as String
import Data.Symbol (class IsSymbol, SProxy)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Halogen (HalogenM, Slot, liftEffect, query, request)
import Halogen.HTML (ClassName(ClassName), ComponentHTML, HTML, br_, button, code_, div, div_, h3_, pre_, slot, small, strong_, text)
import Halogen.HTML.Events (onClick, onDragOver, onDrop)
import Halogen.HTML.Properties (class_, classes, disabled, id_)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError), Warning, _Warning, InterpreterResult, _InterpreterResult)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Prelude (class Ord, Unit, bind, const, discard, join, map, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import Prim.Row as Row
import Servant.PureScript.Ajax (AjaxError)
import StaticData as StaticData
import Types (ChildSlots, HAction(ScrollTo, LoadScript, CompileProgram, HandleEditorMessage, HandleDropEvent, HandleDragEvent), _editorSlot, _warnings)

loadBuffer :: Effect (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.bufferLocalStorageKey

initEditor ∷
  forall m.
  MonadAff m =>
  Maybe String -> Editor -> m Unit
initEditor initialContents editor =
  liftEffect
    $ do
        savedContents <- liftEffect loadBuffer
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
  forall m a.
  MonadAff m =>
  Maybe String -> CompilationState a -> ComponentHTML HAction ChildSlots m
editorPane initialContents state =
  div_
    [ div
        [ id_ "editor"
        , onDragOver $ Just <<< HandleDragEvent
        , onDrop $ Just <<< HandleDropEvent
        ]
        [ slot
            _editorSlot
            unit
            (aceComponent (initEditor initialContents) (Just Live))
            unit
            (Just <<< HandleEditorMessage)
        ]
    , br_
    , div_
        [ button
            [ id_ "compile"
            , classes [ btn, btnClass ]
            , onClick $ const $ Just $ CompileProgram
            , disabled (isLoading state)
            ]
            [ btnText ]
        ]
    , br_
    , errorList
    , warningList
    ]
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

demoScriptsPane :: forall p. HTML p HAction
demoScriptsPane =
  div [ id_ "demos" ]
    ( Array.cons (strong_ [ text "Demos: " ]) (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles))
    )

demoScriptButton :: forall p. String -> HTML p HAction
demoScriptButton key =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ const $ Just $ LoadScript key
    ]
    [ text key ]

interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p HAction)
interpreterErrorPane (TimeoutError error) = [ listGroupItem_ [ div_ [ text error ] ] ]

interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

compilationErrorPane :: forall p. CompilationError -> HTML p HAction
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

compilationWarningsPane :: forall p. Array Warning -> HTML p HAction
compilationWarningsPane warnings = listGroup_ (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

compilationWarningPane :: forall p. Warning -> HTML p HAction
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
