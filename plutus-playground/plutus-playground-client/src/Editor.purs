module Editor
       ( editorPane
       ) where

import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, Autocomplete(Live), aceComponent)
import Ace.Types (ACE, Editor)
import AjaxUtils (showAjaxError)
import Bootstrap (alertDanger_, btn, btnDanger, btnPrimary, btnSecondary, btnSuccess, empty, listGroupItem_, listGroup_, pullRight)
import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff.Class (liftEff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(Just))
import Data.String as String
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), HTML, br_, button, code_, div, div_, h2_, h3_, pre_, slot', small, text)
import Halogen.HTML.Events (input, input_, onClick)
import Halogen.HTML.Properties (class_, classes, disabled)
import Icons (Icon(..), icon)
import Network.RemoteData (RemoteData(..), isLoading)
import Playground.API (CompilationError(CompilationError, RawError))
import Prelude (Unit, bind, discard, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import Types (EditorSlot(..), ChildQuery, ChildSlot, Query(..), State, cpEditor)

editorPane ::
  forall m aff.
  MonadAff (AceEffects aff) m
  => State -> ParentHTML Query ChildQuery ChildSlot m
editorPane state =
  div_
    [ h2_ [ text "Editor" ]
    , slot' cpEditor EditorSlot
        (aceComponent (initEditor state.editorContents) (Just Live))
        unit
        (input HandleEditorMessage)
    , br_
    , div_
        [ button
            [ classes [ btn, btnClass ]
            , onClick $ input_ CompileProgram
            , disabled (isLoading state.compilationResult)
            ]
            [ btnText ]
        ]
    , br_
    , errorList
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
                      alertDanger_
                        [ text $ showAjaxError error
                        , br_
                        , text "Please try again or contact support for assistance."
                        ]
                    _ -> empty

initEditor ∷
  forall m aff.
  MonadAff (ace :: ACE | aff) m
  => String -> Editor -> m Unit
initEditor contents editor = liftEff $ do
  void $ Editor.setValue contents (Just 1) editor
  Editor.setTheme "ace/theme/monokai" editor
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session


compilationErrorPane :: forall p. CompilationError -> HTML p (Query Unit)
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
