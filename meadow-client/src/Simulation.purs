module Simulation where
  
import API (RunResult(RunResult))
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Halogen.Component (AceEffects, Autocomplete(Live), aceComponent)
import Ace.Types (ACE, Editor)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnDanger, btnInfo, btnPrimary, btnSecondary, btnSmall, btnSuccess, cardBody_, card_, col6_, col_, empty, listGroupItem_, listGroup_, pullRight, row_)
import Control.Alternative (map, (<|>))
import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (liftEff)
import DOM.HTML.History (state)
import Data.Array (concatMap, fromFoldable, mapWithIndex, updateAt)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Int as Int
import Data.Lens (over, set, to, view)
import Data.Map as Map
import Data.Maybe (Maybe(Just), fromMaybe)
import Data.Maybe as Maybe
import Data.String as String
import Gists (gistControls)
import Halogen (HTML, action)
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), b_, br_, button, code_, col, colgroup, div, div_, h2_, h3_, input, pre_, slot', small, strong_, table_, td, td_, text, th, th_, tr)
import Halogen.HTML.Events (input_, onChecked, onClick, onDragOver, onDrop, onValueChange)
import Halogen.HTML.Events as Events
import Halogen.HTML.Properties (InputType(..), class_, classes, disabled, placeholder, type_, value)
import Halogen.Query as HQ
import Icons (Icon(..), icon)
import Language.Haskell.Interpreter (CompilationError(CompilationError, RawError))
import LocalStorage (LOCALSTORAGE)
import LocalStorage as LocalStorage
import Network.RemoteData (RemoteData(Success, Failure, Loading, NotAsked), isLoading)
import Prelude (Unit, bind, const, discard, pure, show, unit, void, ($), (<$>), (<<<), (<>))
import StaticData as StaticData
import Types (ChildQuery, ChildSlot, MarloweAction(..), MarloweEditorSlot(MarloweEditorSlot), Person, Query(..), State, _authStatus, _createGistResult, _marloweState, _people, _signed, _suggestedActions, cpMarloweEditor)

simulationPane :: forall m aff. MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff )) m =>
    State -> ParentHTML Query ChildQuery ChildSlot m
simulationPane state =
  div_
    [ row_ [ inputComposerPane state
           , transactionComposerPane state
           , statePane state
           ]
    , demoScriptsPane
    , h2_ [ text "Debugger" ]
    , div
        [ onDragOver $ Just <<< action <<< HandleDragEvent
        , onDrop $ Just <<< action <<< HandleDropEvent
        ]
        [ slot' cpMarloweEditor MarloweEditorSlot
            (aceComponent initEditor (Just Live))
            unit
            (Events.input HandleEditorMessage)
        ]
    , br_
    , div_
        [ div [ class_ pullRight ]
            [ gistControls (view _authStatus state) (view _createGistResult state) ]
        ]
    , br_
    , runResult
    , errorList
    ]
  where
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
loadBuffer = LocalStorage.getItem StaticData.marloweBufferLocalStorageKey

initEditor ∷
  forall m aff.
  MonadAff (ace :: ACE, localStorage :: LOCALSTORAGE | aff) m
  => Editor -> m Unit
initEditor editor = liftEff $ do
  savedContents <- liftEff loadBuffer
  let defaultContents = Just StaticData.marloweContract
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

inputComposerPane :: forall p. State -> HTML p Query
inputComposerPane state =
    col6_ 
        [ h2_ [ text "Input Composer" ]
        , div [ class_ $ ClassName "wallet" ]
              [ card_
                  [ cardBody_ (concatMap inputComposerPerson (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state))
                  ]
              ]
        ]

inputComposerPerson :: forall p. Person -> Array (HTML p Query)
inputComposerPerson person = [ h3_ [ text ("Person " <> show person.id)]] <> mapWithIndex (suggestedActionRow person) person.suggestedActions

updateSuggestedAction :: Person -> Int -> MarloweAction -> Person
updateSuggestedAction person idx val = over _suggestedActions 
                                            (\acts -> Maybe.fromMaybe acts (updateAt idx val acts))
                                            person

marloweActionInput :: forall p. Person -> Int -> (Int -> MarloweAction) -> Int -> HTML p Query
marloweActionInput person idx f current
    = input [ type_ InputNumber
            , placeholder "Int"
            , value $ show current
            , onValueChange $ map (HQ.action <<< UpdatePerson <<< \val -> (updateSuggestedAction person idx (f val))) <<< Int.fromString
            ]

promoteAction :: Person -> Int -> Person
promoteAction person idx = fromMaybe person $ do
    act <- Array.index person.suggestedActions idx 
    suggestedActions <- Array.deleteAt idx person.suggestedActions
    let actions = Array.snoc person.actions act
    pure $ person { actions = actions
                  , suggestedActions = suggestedActions
                  }

suggestedActionRow :: forall p. Person -> Int -> MarloweAction -> HTML p Query
suggestedActionRow person idx (Commit v i e) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button" 
                                         , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                         ]
                                         [ text "+" ]
                                , text "Commit " 
                                , marloweActionInput person idx (\val -> (Commit val i e)) v
                                , text " ADA with id "
                                , marloweActionInput person idx (\val -> (Commit v val e)) i
                                , text " to expire by "
                                , marloweActionInput person idx (\val -> (Commit v i val)) e
                                ]
                            ]
suggestedActionRow person idx (Redeem v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                         ]
                                         [ text "+" ]
                                , text "Redeem " 
                                , marloweActionInput person idx (\val -> (Redeem val i)) v
                                , text " ADA from id "
                                , marloweActionInput person idx (\val -> (Redeem v val)) i
                                ]
                            ]
suggestedActionRow person idx (Claim v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                         ]
                                         [ text "+" ]
                                , text "Claim " 
                                , marloweActionInput person idx (\val -> (Claim val i)) v
                                , text " ADA from id "
                                , marloweActionInput person idx (\val -> (Claim v val)) i
                                ]
                            ]
suggestedActionRow person idx (Choose v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                         ]
                                         [ text "+" ]
                                , text "Choose value " 
                                , marloweActionInput person idx (\val -> (Choose val i)) v
                                , text " for id "
                                , marloweActionInput person idx (\val -> (Choose v val)) i
                                ]
                            ]


transactionComposerPane :: forall p. State -> HTML p Query
transactionComposerPane state =
    col6_
        [ h2_ [ text "Transaction Composer" ]
        , div [ class_ $ ClassName "wallet" ]
              [ card_
                  [ cardBody_ $
                    (concatMap transactionComposerPerson (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state))
                    <> signatures (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state)
                    <> transactionButtons
                  ]
             ]
        ]

transactionButtons :: forall p. Array (HTML p Query)
transactionButtons = [ row_
                        [ col_ 
                            [ button 
                                [ classes [btn, btnPrimary ]
                                , onClick $ Just <<< HQ.action <<< const ApplyTrasaction
                                ]
                                [ text "Apply Transaction" ]
                            , button 
                                [ classes [btn, btnPrimary ] 
                                , onClick $ Just <<< HQ.action <<< const NextBlock
                                ]
                                [ text "Next Block" ]
                            ]
                        ]
                     ]

signatures :: forall p. Array Person -> Array (HTML p Query)
signatures people = [ h3_ [ text "Signatures" ]
                    , row_ (map signature people)
                    ]

signature :: forall p. Person -> HTML p Query
signature person = col_ [ input [ type_ InputCheckbox
                                , onChecked $ Just <<< HQ.action <<< UpdatePerson <<< (\checked -> set _signed checked person)
                                ]
                        , text $ "Person " <> show person.id
                        ]

transactionComposerPerson :: forall p. Person -> Array (HTML p Query)
transactionComposerPerson person = [ h3_ [ text ("Person " <> show person.id)]] <> mapWithIndex (actionRow person) person.actions

actionRow :: forall p. Person -> Int -> MarloweAction -> HTML p Query
actionRow person idx (Commit v i e) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                         ]
                                         [ text "-" ]
                                , text "Commit "
                                , b_ [ text (show v) ]
                                , text " ADA with id "
                                , b_ [ text (show i) ]
                                , text " to expire by "
                                , b_ [ text (show e) ]
                                ]
                            ]
actionRow person idx (Redeem v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                         ]
                                         [ text "-" ]
                                , text "Redeem " 
                                , b_ [ text (show v) ]
                                , text " ADA from id "
                                , b_ [ text (show i) ]
                                ]
                            ]
actionRow person idx (Claim v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button"
                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                         ]
                                         [ text "-" ]
                                , text "Claim " 
                                , b_ [ text (show v) ]
                                , text " ADA from id "
                                , b_ [ text (show i) ]
                                ]
                            ]
actionRow person idx (Choose v i) = row_
                            [ col_
                                [ button [ class_ $ ClassName "composer-add-button" 
                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                         ]
                                         [ text "-" ]
                                , text "Choose value " 
                                , b_ [ text (show v) ]
                                , text " for id "
                                , b_ [ text (show i) ]
                                ]
                            ]

demoteAction :: Person -> Int -> Person
demoteAction person idx = fromMaybe person $ do
    act <- Array.index person.actions idx 
    actions <- Array.deleteAt idx person.actions
    let suggestedActions = Array.snoc person.suggestedActions act
    pure $ person { actions = actions
                  , suggestedActions = suggestedActions
                  }           

statePane :: forall p. State -> HTML p Query
statePane state = div [ class_ $ ClassName "col" ] 
                        [ strong_ [ text "Current Block:" ]
                        , text (show state.marloweState.state)
                        , h2_ [ text "State" ]
                        , stateTable state
                        ]

stateTable :: forall p. State -> HTML p Query
stateTable state = div [ class_ $ ClassName "full-width-card" ]
                       [ card_ [ cardBody_ [ row_ [ stateRow state ]
                                           , row_ [ stateRow state ]
                                           , row_ [ stateRow state ]
                                           ]
                               ]
                       ]

stateRow :: forall p. State -> HTML p Query
stateRow state = table_ [ colgroup []
                                   [ col []
                                   , col []
                                   , col []
                                   ]
                        , tr [] [ th_ [ text "Commit" ]
                                , th [ class_ $ ClassName "middle-column" ] [ text "Person" ]
                                , th_ [ text "Value"  ]
                                ]
                        , tr [] [ td_ [ text "1" ]
                                , td [ class_ $ ClassName "middle-column" ] [ text "2" ]
                                , td_ [ text "50 ADA" ]
                                ]
                        ]