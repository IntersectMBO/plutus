module Editor
       ( editorPane
       ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, Autocomplete(Live), aceComponent)
import Ace.Types (ACE, Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, col10_, col2_, empty, listGroupItem_, listGroup_, pullRight, row_)
import Control.Alternative ((<|>))
import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Lens (view, to)
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
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(..), isLoading)
import Playground.API (_CompilationResult, CompilationError(CompilationError, RawError), Warning, _Warning)
import Prelude (Unit, bind, discard, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import StaticData as StaticData
import Types (ChildQuery, ChildSlot, EditorSlot(..), Query(..), State, _authStatus, _createGistResult, _warnings, cpEditor)

editorPane ::
  forall m aff.
  MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff)) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
editorPane state =
  div_
    [ demoScriptsPane
    , div
        [ onDragOver $ Just <<< action <<< HandleDragEvent
        , onDrop $ Just <<< action <<< HandleDropEvent
        ]
        [ slot' cpEditor EditorSlot
            (aceComponent initEditor (Just Live))
            unit
            (input HandleEditorMessage)
        ]
    , br_
    , row_
        [ col10_
            [ button
                [ classes [ btn, btnClass ]
                , onClick $ input_ CompileProgram
                , disabled (isLoading state.compilationResult)
                ]
                [ btnText ]
            ]
        , col2_
            [ gistControls (view _authStatus state) (view _createGistResult state) ]
        ]
    , br_
    , errorList
    , warningList
    ]
    where
      btnClass = case state.compilationResult of
                   Success (Right _) -> btnSuccess
                   Success (Left _) -> btnDanger
                   Failure _ -> btnDanger
                   Loading -> btnSecondary
                   NotAsked -> btnPrimary
      btnText = case state.compilationResult of
                   Loading -> icon Spinner
                   _ -> text "Compile"
      errorList = case state.compilationResult of
                    (Success (Left errors)) ->
                      listGroup_
                        (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
                    Failure error ->
                      ajaxErrorPane error
                    _ -> empty
      warningList = case state.compilationResult of
                     (Success (Right result)) -> view (_CompilationResult <<< _warnings <<< to compilationWarningsPane) result
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

demoScriptsPane :: forall p. HTML p Query
demoScriptsPane =
  div [ class_ $ ClassName "demos" ]
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
compilationWarningsPane warnings = listGroup_ $ listGroupItem_ <<< pure <<< compilationWarningPane <$> warnings

compilationWarningPane :: forall p. Warning -> HTML p Query
compilationWarningPane warning = div [ class_ $ ClassName "compilation-warning" ] [ text (view _Warning warning) ]
