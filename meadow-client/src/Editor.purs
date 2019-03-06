module Editor
       ( editorPane
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
import Gists (gistControls)
import Halogen (HTML, action)
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), br_, button, code_, div, div_, h3_, pre_, slot', small, strong_, text)
import Halogen.HTML.Events (input, input_, onClick, onDragOver, onDrop)
import Halogen.HTML.Properties (class_, classes, disabled)
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError))
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), _Success, isLoading)
import API (_RunResult, RunResult(..))
import Prelude (Unit, bind, discard, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import StaticData as StaticData
import Types (ChildQuery, ChildSlot, EditorSlot(..), Query(..), State, _authStatus, _runResult, _createGistResult, cpEditor)

editorPane ::
  forall m aff.
  MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
editorPane state =
  div_
    [ div
        [ onDragOver $ Just <<< action <<< HandleDragEvent
        , onDrop $ Just <<< action <<< HandleDropEvent
        ]
        [ slot' cpEditor EditorSlot
            (aceComponent initEditor (Just Live))
            unit
            (input HandleEditorMessage)
        ]
    , br_
    , div_
        [ div [ class_ pullRight ]
            [ gistControls (view _authStatus state) (view _createGistResult state) ]
        , div_
            [ button
                [ classes [ btn, btnClass ]
                , onClick $ input_ CompileProgram
                , disabled (isLoading state.runResult)
                ]
                [ btnText ]
            ]
        ]
    , br_
    , runResult
    , errorList
    ]
  where
    btnClass = case state.runResult of
                 Success (Right _) -> btnSuccess
                 Success (Left _) -> btnDanger
                 Failure _ -> btnDanger
                 Loading -> btnSecondary
                 NotAsked -> btnPrimary
    btnText = case state.runResult of
                 Loading -> icon Spinner
                 _ -> text "Compile"
    errorList = case state.runResult of
                  Success (Left errors) ->
                    listGroup_
                      (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
                  Failure error ->
                    ajaxErrorPane error
                  _ -> empty
    runResult = case state.runResult of
                  Success (Right stdout) ->
                    listGroup_
                      [(listGroupItem_ <<< pure <<< compilationResultPane $ stdout)]
                  _ -> empty

loadBuffer :: forall eff. Eff (localStorage :: LOCALSTORAGE | eff) (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.bufferLocalStorageKey

initEditor ∷
  forall m aff.
  MonadAff (ace :: ACE, localStorage :: LOCALSTORAGE | aff) m
  => Editor -> m Unit
initEditor editor = liftEff $ do
  savedContents <- liftEff loadBuffer
  let defaultContents = Map.lookup "Vesting" StaticData.demoFiles
  let contents = fromMaybe "" (savedContents <|> defaultContents)
  void $ Editor.setValue contents (Just 1) editor

  Editor.setTheme "ace/theme/monokai" editor
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session

compilationResultPane :: forall p. RunResult -> HTML p Query
compilationResultPane (RunResult stdout) =
  div_ [ code_ [ pre_ [ text stdout ] ] ]

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