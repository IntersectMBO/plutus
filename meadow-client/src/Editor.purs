module Editor
  ( editorPane
  ) where

import API
  ( RunResult(..)
  )
import Ace.Halogen.Component
  ( AceEffects
  , Autocomplete
      ( Live
      )
  , aceComponent
  )
import Ace.Types
  ( ACE
  , Editor
  )
import AjaxUtils
  ( ajaxErrorPane
  )
import Bootstrap
  ( btn
  , btnDanger
  , btnInfo
  , btnPrimary
  , btnSecondary
  , btnSmall
  , btnSuccess
  , empty
  , listGroupItem_
  , listGroup_
  , pullRight
  )
import Control.Alternative
  ( (<|>)
  )
import Control.Monad.Aff.Class
  ( class MonadAff
  )
import Control.Monad.Eff
  ( Eff
  )
import Control.Monad.Eff.Class
  ( liftEff
  )
import Data.Either
  ( Either(..)
  )
import Data.Lens
  ( view
  )
import Data.Maybe
  ( Maybe
      ( Just
      )
  , fromMaybe
  )
import Gists
  ( gistControls
  )
import Halogen
  ( HTML
  , action
  )
import Halogen.Component
  ( ParentHTML
  )
import Halogen.HTML
  ( ClassName
      ( ClassName
      )
  , br_
  , button
  , code_
  , div
  , div_
  , h3_
  , pre_
  , slot'
  , small
  , strong_
  , text
  )
import Halogen.HTML.Events
  ( input
  , input_
  , onClick
  , onDragOver
  , onDrop
  )
import Halogen.HTML.Properties
  ( class_
  , classes
  , disabled
  )
import Data.HeytingAlgebra
  ( (||)
  )
import Icons
  ( Icon(..)
  , icon
  )
import Language.Haskell.Interpreter
  ( CompilationError
      ( CompilationError
      , RawError
      )
    , InterpreterError (CompilationErrors, TimeoutError)
  )
import LocalStorage
  ( LOCALSTORAGE
  )
import Network.RemoteData
  ( RemoteData(..)
  , isLoading
  )
import Prelude
  ( Unit
  , bind
  , discard
  , pure
  , show
  , unit
  , void
  , map
  , not
  , ($)
  , (<$>)
  , (<<<)
  , (<>)
  )
import Types
  ( ChildQuery
  , ChildSlot
  , EditorSlot(..)
  , Query(..)
  , FrontendState
  , _authStatus
  , _createGistResult
  , cpEditor
  )

import Ace.EditSession as Session
import Ace.Editor as Editor
import Data.Array as Array
import Data.Map as Map
import Data.String as String
import LocalStorage as LocalStorage
import StaticData as StaticData

isSuccess :: forall r e a. RemoteData r (Either e a) -> Boolean
isSuccess (Success (Right _)) = true
isSuccess _ = false

editorPane ::
  forall m aff.
  MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff)) m
  => FrontendState -> ParentHTML Query ChildQuery ChildSlot m
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
    , div_
        [ div [ class_ pullRight ]
            [ gistControls
                (view _authStatus state)
                (view _createGistResult state)
            ]
        , div_
            [ button
                [ classes [ btn, btnClass ]
                , onClick $ input_ CompileProgram
                , disabled (isLoading state.runResult)
                ]
                [ btnText ]
            , button [ classes [ btn
                               , btnPrimary 
                               ]
                     , onClick $ input_ SendResult
                     , disabled ((isLoading state.runResult) || ((not isSuccess) state.runResult))
                     ] [ text "Send to Simulator" ]
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
    Success (Left error) -> listGroup_ (interpreterErrorPane error)
    Failure error -> ajaxErrorPane error
    _ -> empty
  runResult = case state.runResult of
    Success (Right stdout) -> listGroup_ [ (listGroupItem_ <<< pure <<< compilationResultPane $ stdout)
                                         ]
    _ -> empty

loadBuffer ::
  forall eff.
  Eff (localStorage :: LOCALSTORAGE | eff) (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.bufferLocalStorageKey

initEditor ::
  forall m aff.
  MonadAff (ace :: ACE, localStorage :: LOCALSTORAGE | aff) m =>
  Editor ->
  m Unit
initEditor editor = liftEff $ do
  savedContents <- liftEff loadBuffer
  let defaultContents = Map.lookup "BasicContract" StaticData.demoFiles
  let contents = fromMaybe "" (savedContents <|> defaultContents)
  void $ Editor.setValue contents (Just 1) editor
  Editor.setTheme "ace/theme/monokai" editor
  --
  --
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session

demoScriptsPane ::
  forall p.
  HTML p Query
demoScriptsPane = div [ class_ $ ClassName "demos"
                      ] (Array.cons (strong_ [ text "Demos: "
                                             ]) (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.demoFiles)))

demoScriptButton ::
  forall p.
  String ->
  HTML p Query
demoScriptButton key = button [ classes [ btn
                                        , btnInfo
                                        , btnSmall
                                        ]
                              , onClick $ input_ $ LoadScript key
                              ] [ text key
                                ]

compilationResultPane ::
  forall p.
  RunResult ->
  HTML p Query
compilationResultPane (RunResult stdout) = div_ [ code_ [ pre_ [ text stdout
                                                               ]
                                                        ]
                                                ]

interpreterErrorPane :: forall p. InterpreterError -> Array (HTML p Query)
interpreterErrorPane (TimeoutError error) = [listGroupItem_ [div_ [ text error ]]]
interpreterErrorPane (CompilationErrors errors) = map compilationErrorPane errors

compilationErrorPane :: forall p. CompilationError -> HTML p Query
compilationErrorPane (RawError error) = listGroupItem_ [div_ [ text error ]]
compilationErrorPane (CompilationError error) = listGroupItem_ [
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
  ]