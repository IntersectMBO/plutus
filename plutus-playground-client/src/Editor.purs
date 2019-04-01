module Editor
       ( editorPane
       , demoScriptsPane
       ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, Autocomplete(Live), aceComponent)
import Ace.Types (ACE, Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, empty, listGroupItem_, listGroup_, pullRight)
import Control.Alternative ((<|>))
import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (_Right, preview, to, view)
import Data.Map as Map
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.String as String
import Halogen (HTML, action)
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), br_, button, code_, div, div_, h3_, pre_, slot', small, strong_, text)
import Halogen.HTML.Events (input, input_, onClick, onDragOver, onDrop)
import Halogen.HTML.Properties (class_, classes, disabled, id_)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError), InterpreterError(CompilationErrors, TimeoutError))
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import Playground.API (_CompilationResult, Warning, _Warning)
import Prelude (Unit, bind, discard, pure, show, unit, void, ($), (<$>), (<<<), (<>), map)
import StaticData as StaticData
import Types (ChildQuery, ChildSlot, EditorSlot(EditorSlot), Query(ScrollTo, LoadScript, CompileProgram, HandleEditorMessage, HandleDropEvent, HandleDragEvent), State, _compilationResult, _warnings, cpEditor)

loadBuffer :: forall eff. Eff (localStorage :: LOCALSTORAGE | eff) (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.bufferLocalStorageKey

initialContents :: Maybe String
initialContents = Map.lookup "Vesting" StaticData.demoFiles

initEditor ∷
  forall m aff.
  MonadAff (ace :: ACE, localStorage :: LOCALSTORAGE | aff) m
  => Editor -> m Unit
initEditor editor = liftEff $ do
  savedContents <- liftEff loadBuffer
  let contents = fromMaybe "" (savedContents <|> initialContents)
  void $ Editor.setValue contents (Just 1) editor

  Editor.setTheme "ace/theme/monokai" editor
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session

editorPane ::
  forall m aff.
  MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
editorPane state =
  div_
    [ div
        [ id_ "editor"
        , onDragOver $ Just <<< action <<< HandleDragEvent
        , onDrop $ Just <<< action <<< HandleDropEvent
        ]
        [ slot' cpEditor EditorSlot
            (aceComponent initEditor (Just Live))
            unit
            (input HandleEditorMessage)
        ]
    , br_
    , div_
        [ button
            [ id_ "compile"
            , classes [ btn, btnClass ]
            , onClick $ input_ CompileProgram
            , disabled (isLoading (view _compilationResult state))
            ]
            [ btnText ]
        ]
    , br_
    , errorList
    , warningList
    ]
  where
    btnClass = case view _compilationResult state of
                 Success (Right _) -> btnSuccess
                 Success (Left _) -> btnDanger
                 Failure _ -> btnDanger
                 Loading -> btnSecondary
                 NotAsked -> btnPrimary
    btnText = case view _compilationResult state of
                 Loading -> icon Spinner
                 _ -> text "Compile"
    errorList = case view _compilationResult state of
                  Success (Left error) -> listGroup_ (interpreterErrorPane error)
                  Failure error -> ajaxErrorPane error
                  _ -> empty
    warningList =
      fromMaybe empty $
        preview
          (_compilationResult <<<
             _Success <<<
             _Right <<<
             _CompilationResult <<<
             _warnings <<<
             to compilationWarningsPane)
          state

demoScriptsPane :: forall p. HTML p Query
demoScriptsPane =
  div [ id_ "demos" ]
   (Array.cons
      (strong_ [ text "Demos: " ])
      (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles)))

demoScriptButton :: forall p. String -> HTML p Query
demoScriptButton key =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ input_ $ LoadScript key
    ]
    [ text key ]

interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p Query)
interpreterErrorPane (TimeoutError error) = [listGroupItem_ [div_ [ text error ]]]
interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

compilationErrorPane :: forall p. CompilationError -> HTML p Query
compilationErrorPane (RawError error) =
  div_ [ text error ]
compilationErrorPane (CompilationError error) =
  div [ class_ $ ClassName "compilation-error"
      , onClick $ input_ $ ScrollTo {row: error.row, column: error.column}
      ]
    [ small [ class_ pullRight ]
        [ text "jump" ]
    , h3_
        [ text $ "Line " <> show error.row <> ", Column " <> show error.column <> ":" ]
    , code_
        [ pre_ [ text $ String.joinWith "\n" error.text ] ]
    ]

compilationWarningsPane :: forall p. Array Warning -> HTML p Query
compilationWarningsPane warnings =
  listGroup_
    (listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings)

compilationWarningPane :: forall p. Warning -> HTML p Query
compilationWarningPane warning =
  div [ class_ $ ClassName "compilation-warning" ]
    [ text $ view _Warning warning ]
