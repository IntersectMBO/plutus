module Simulation where

import API
  ( RunResult
      ( RunResult
      )
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
  , btnInfo
  , btnPrimary
  , btnSmall
  , cardBody_
  , card_
  , col6
  , col_
  , empty
  , listGroupItem_
  , listGroup_
  , pullRight
  , row_
  )
import Control.Alternative
  ( map
  , (<|>)
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
import Data.Array
  ( concatMap
  , fromFoldable
  , mapWithIndex
  , updateAt
  )
import Data.Either
  ( Either(..)
  )
import Data.Lens
  ( over
  , set
  , to
  , view
  )
import Data.Maybe
  ( Maybe
      ( Just
      )
  , fromMaybe
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
  , b_
  , br_
  , button
  , code_
  , col
  , colgroup
  , div
  , div_
  , h2
  , h3_
  , input
  , pre_
  , slot'
  , small
  , span_
  , span
  , strong_
  , table_
  , tbody_
  , td
  , td_
  , text
  , th
  , th_
  , thead_
  , tr
  )
import Halogen.HTML.Events
  ( input_
  , onChecked
  , onClick
  , onDragOver
  , onDrop
  , onValueChange
  )
import Halogen.HTML.Properties
  ( InputType(..)
  , class_
  , classes
  , placeholder
  , type_
  , value
  )
import Language.Haskell.Interpreter
  ( CompilationError
      ( CompilationError
      , RawError
      )
  )
import LocalStorage
  ( LOCALSTORAGE
  )
import Network.RemoteData
  ( RemoteData
      ( Success
      , Failure
      )
  )
import Prelude
  ( Unit
  , bind
  , const
  , discard
  , pure
  , show
  , unit
  , void
  , ($)
  , (<$>)
  , (<<<)
  , (<>)
  )
import Types
  ( ChildQuery
  , ChildSlot
  , MarloweAction(..)
  , MarloweEditorSlot
      ( MarloweEditorSlot
      )
  , MarloweError(..)
  , Person
  , Query(..)
  , State
  , _marloweState
  , _people
  , _signed
  , _suggestedActions
  , cpMarloweEditor
  )

import Ace.EditSession as Session
import Ace.Editor as Editor
import Data.Array as Array
import Data.Int as Int
import Data.Map as Map
import Data.Maybe as Maybe
import Data.String as String
import Halogen.HTML.Events as Events
import Halogen.Query as HQ
import LocalStorage as LocalStorage
import StaticData as StaticData

paneHeader ::
  forall p.
  String ->
  HTML p Query
paneHeader s = h2 [ class_ $ ClassName "pane-header"
                  ] [ text s
                    ]

simulationPane ::
  forall m aff.
  MonadAff (AceEffects (localStorage :: LOCALSTORAGE | aff)) m =>
  State ->
  ParentHTML Query ChildQuery ChildSlot m
simulationPane state = div_ [ row_ [ inputComposerPane state
                                   , transactionComposerPane state
                                   ]
                            , stateTitle state
                            , row_ [ statePane state
                                   ]
                            , div [ classes [ ClassName "demos"
                                            , ClassName "d-flex"
                                            , ClassName "flex-row"
                                            , ClassName "align-items-center"
                                            , ClassName "justify-content-between"
                                            , ClassName "mt-5"
                                            , ClassName "mb-3"
                                            ]
                                  ] [ paneHeader "Debugger"
                                    , demoScriptsPane
                                    ]
                            , div [ onDragOver $ Just <<< action <<< MarloweHandleDragEvent
                                  , onDrop $ Just <<< action <<< MarloweHandleDropEvent
                                  ] [ slot' cpMarloweEditor MarloweEditorSlot (aceComponent initEditor (Just Live)) unit (Events.input MarloweHandleEditorMessage)
                                    ]
                            , br_
                            , errorList
                            ]
  where
  errorList = case state.marloweCompileResult of
    Left errors -> listGroup_ (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
    _ -> empty

loadBuffer ::
  forall eff.
  Eff (localStorage :: LOCALSTORAGE | eff) (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.marloweBufferLocalStorageKey

initEditor ::
  forall m aff.
  MonadAff (ace :: ACE, localStorage :: LOCALSTORAGE | aff) m =>
  Editor ->
  m Unit
initEditor editor = liftEff $ do
  savedContents <- liftEff loadBuffer
  let defaultContents = Map.lookup "Deposit Insentive" StaticData.marloweContracts
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
demoScriptsPane = div_ (Array.cons (strong_ [ text "Demos: "
                                            ]) (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.marloweContracts)))

demoScriptButton ::
  forall p.
  String ->
  HTML p Query
demoScriptButton key = button [ classes [ btn
                                        , btnInfo
                                        , btnSmall
                                        ]
                              , onClick $ input_ $ LoadMarloweScript key
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

compilationErrorPane ::
  forall p.
  MarloweError ->
  HTML p Query
compilationErrorPane (MarloweError error) = div_ [ text error
                                                 ]

inputComposerPane ::
  forall p.
  State ->
  HTML p Query
inputComposerPane state = div [ classes [ col6
                                        , ClassName "input-composer"
                                        ]
                              ] [ paneHeader "Input Composer"
                                , div [ class_ $ ClassName "wallet"
                                      ] [ card_ [ cardBody_ (concatMap inputComposerPerson (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state))
                                                ]
                                        ]
                                ]

inputComposerPerson ::
  forall p.
  Person ->
  Array (HTML p Query)
inputComposerPerson person = [ h3_ [ text ("Person " <> show person.id)
                                   ]
                             ] <> mapWithIndex (suggestedActionRow person) person.suggestedActions

updateSuggestedAction ::
  Person ->
  Int ->
  MarloweAction ->
  Person
updateSuggestedAction person idx val = over _suggestedActions (\acts ->
  Maybe.fromMaybe acts (updateAt idx val acts)) person

marloweActionInput ::
  forall p.
  Person ->
  Int ->
  (Int -> MarloweAction) ->
  Int ->
  HTML p Query
marloweActionInput person idx f current = input [ type_ InputNumber
                                                , placeholder "Int"
                                                , class_ $ ClassName "action-input"
                                                , value $ show current
                                                , onValueChange $ map (HQ.action <<< UpdatePerson <<< \val ->
                                                  (updateSuggestedAction person idx (f val))) <<< Int.fromString
                                                ]

promoteAction ::
  Person ->
  Int ->
  Person
promoteAction person idx = fromMaybe person $ do
  act <- Array.index person.suggestedActions idx
  suggestedActions <- Array.deleteAt idx person.suggestedActions
  let actions = Array.snoc person.actions act
  pure $ person { actions = actions
                , suggestedActions = suggestedActions
                }

flexRow_ ::
  forall p.
  Array (HTML p Query) ->
  HTML p Query
flexRow_ html = div [ classes [ ClassName "d-flex"
                              , ClassName "flex-row"
                              ]
                    ] html

spanText ::
  forall p.
  String ->
  HTML p Query
spanText s = span [ class_ $ ClassName "pr-1"
                  ] [ text s
                    ]

suggestedActionRow ::
  forall p.
  Person ->
  Int ->
  MarloweAction ->
  HTML p Query
suggestedActionRow person idx (Commit v i e) = flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                                                                 , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                                                 ] [ text "+"
                                                                   ]
                                                        , spanText "Commit "
                                                        , marloweActionInput person idx (\val ->
                                                          (Commit val i e)) v
                                                        , spanText " ADA with id "
                                                        , marloweActionInput person idx (\val ->
                                                          (Commit v val e)) i
                                                        , spanText " to expire by "
                                                        , marloweActionInput person idx (\val ->
                                                          (Commit v i val)) e
                                                        ]

suggestedActionRow person idx (Redeem v i) = flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                                                               , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                                               ] [ text "+"
                                                                 ]
                                                      , spanText "Redeem "
                                                      , marloweActionInput person idx (\val ->
                                                        (Redeem val i)) v
                                                      , spanText " ADA from id "
                                                      , marloweActionInput person idx (\val ->
                                                        (Redeem v val)) i
                                                      ]

suggestedActionRow person idx (Claim v i) = flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                                                              , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                                              ] [ text "+"
                                                                ]
                                                     , spanText "Claim "
                                                     , marloweActionInput person idx (\val ->
                                                       (Claim val i)) v
                                                     , spanText " ADA from id "
                                                     , marloweActionInput person idx (\val ->
                                                       (Claim v val)) i
                                                     ]

suggestedActionRow person idx (Choose v i) = flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                                                               , onClick <<< input_ <<< UpdatePerson $ promoteAction person idx
                                                               ] [ text "+"
                                                                 ]
                                                      , spanText "Choose value "
                                                      , marloweActionInput person idx (\val ->
                                                        (Choose val i)) v
                                                      , spanText " for id "
                                                      , marloweActionInput person idx (\val ->
                                                        (Choose v val)) i
                                                      ]

transactionComposerPane ::
  forall p.
  State ->
  HTML p Query
transactionComposerPane state = div [ classes [ col6
                                              , ClassName "input-composer"
                                              ]
                                    ] [ paneHeader "Transaction Composer"
                                      , div [ class_ $ ClassName "wallet"
                                            ] [ card_ [ cardBody_ $ (concatMap transactionComposerPerson (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state)) <> signatures (view (_marloweState <<< _people <<< to Map.values <<< to fromFoldable) state) <> transactionButtons
                                                      ]
                                              ]
                                      ]

transactionButtons ::
  forall p.
  Array (HTML p Query)
transactionButtons = [ div [ classes [ ClassName "d-flex"
                                     , ClassName "flex-row"
                                     , ClassName "align-items-center"
                                     , ClassName "justify-content-start"
                                     , ClassName "transaction-btn-row"
                                     ]
                           ] [ button [ classes [ btn
                                                , btnPrimary
                                                , ClassName "transaction-btn"
                                                ]
                                      , onClick $ Just <<< HQ.action <<< const ApplyTrasaction
                                      ] [ text "Apply Transaction"
                                        ]
                             , button [ classes [ btn
                                                , btnPrimary
                                                , ClassName "transaction-btn"
                                                ]
                                      , onClick $ Just <<< HQ.action <<< const NextBlock
                                      ] [ text "Next Block"
                                        ]
                             , button [ classes [ btn
                                                , btnPrimary
                                                , ClassName "transaction-btn"
                                                ]
                                      , onClick $ Just <<< HQ.action <<< const CompileMarlowe
                                      ] [ text "Compile"
                                        ]
                             ]
                     ]

signatures ::
  forall p.
  Array Person ->
  Array (HTML p Query)
signatures people = [ h3_ [ text "Signatures"
                          ]
                    , div [ classes [ ClassName "d-flex"
                                    , ClassName "flex-row"
                                    , ClassName "align-items-center"
                                    , ClassName "justify-content-start"
                                    , ClassName "signature-row"
                                    ]
                          ] (map signature people)
                    ]

signature ::
  forall p.
  Person ->
  HTML p Query
signature person = span [ class_ $ ClassName "pr-2"
                        ] [ input [ type_ InputCheckbox
                                  , onChecked $ Just <<< HQ.action <<< UpdatePerson <<< (\checked ->
                                    set _signed checked person)
                                  ]
                          , span_ [ text $ " Person " <> show person.id
                                  ]
                          ]

transactionComposerPerson ::
  forall p.
  Person ->
  Array (HTML p Query)
transactionComposerPerson person = [ h3_ [ text ("Person " <> show person.id)
                                         ]
                                   ] <> mapWithIndex (actionRow person) person.actions

actionRow ::
  forall p.
  Person ->
  Int ->
  MarloweAction ->
  HTML p Query
actionRow person idx (Commit v i e) = row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                                                           , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                                           ] [ text "-"
                                                             ]
                                                  , text "Commit "
                                                  , b_ [ text (show v)
                                                       ]
                                                  , text " ADA with id "
                                                  , b_ [ text (show i)
                                                       ]
                                                  , text " to expire by "
                                                  , b_ [ text (show e)
                                                       ]
                                                  ]
                                           ]

actionRow person idx (Redeem v i) = row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                                         ] [ text "-"
                                                           ]
                                                , text "Redeem "
                                                , b_ [ text (show v)
                                                     ]
                                                , text " ADA from id "
                                                , b_ [ text (show i)
                                                     ]
                                                ]
                                         ]

actionRow person idx (Claim v i) = row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                                                        , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                                        ] [ text "-"
                                                          ]
                                               , text "Claim "
                                               , b_ [ text (show v)
                                                    ]
                                               , text " ADA from id "
                                               , b_ [ text (show i)
                                                    ]
                                               ]
                                        ]

actionRow person idx (Choose v i) = row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                                                         , onClick <<< input_ <<< UpdatePerson $ demoteAction person idx
                                                         ] [ text "-"
                                                           ]
                                                , text "Choose value "
                                                , b_ [ text (show v)
                                                     ]
                                                , text " for id "
                                                , b_ [ text (show i)
                                                     ]
                                                ]
                                         ]

demoteAction ::
  Person ->
  Int ->
  Person
demoteAction person idx = fromMaybe person $ do
  act <- Array.index person.actions idx
  actions <- Array.deleteAt idx person.actions
  let suggestedActions = Array.snoc person.suggestedActions act
  pure $ person { actions = actions
                , suggestedActions = suggestedActions
                }

stateTitle ::
  forall p.
  State ->
  HTML p Query
stateTitle state = div [ classes [ ClassName "demos"
                                 , ClassName "d-flex"
                                 , ClassName "flex-row"
                                 , ClassName "align-items-center"
                                 , ClassName "justify-content-between"
                                 , ClassName "mt-3"
                                 , ClassName "mb-3"
                                 ]
                       ] [ paneHeader "State"
                         , span [ classes [ ClassName "btn"
                                          , ClassName "btn-sm"
                                          ]
                                ] [ strong_ [ text "Current Block:"
                                            ]
                                  , span [ class_ $ ClassName "block-number"
                                         ] [ text (show state.marloweState.state)
                                           ]
                                  ]
                         ]

statePane ::
  forall p.
  State ->
  HTML p Query
statePane state = div [ class_ $ ClassName "col"
                      ] [ stateTable state
                        ]

stateTable ::
  forall p.
  State ->
  HTML p Query
stateTable state = div [ class_ $ ClassName "full-width-card"
                       ] [ card_ [ cardBody_ [ row_ [ stateRow state
                                                    ]
                                             , row_ [ stateRow state
                                                    ]
                                             , row_ [ stateRow state
                                                    ]
                                             ]
                                 ]
                         ]

stateRow ::
  forall p.
  State ->
  HTML p Query
stateRow state = table_ [ colgroup [] [ col []
                                      , col []
                                      , col []
                                      ]
                        , thead_ [ tr [] [ th_ [ text "Commit"
                                               ]
                                         , th [ class_ $ ClassName "middle-column"
                                              ] [ text "Person"
                                                ]
                                         , th_ [ text "Value"
                                               ]
                                         ]
                                 ]
                        , tbody_ [ tr [] [ td_ [ text "1"
                                               ]
                                         , td [ class_ $ ClassName "middle-column"
                                              ] [ text "2"
                                                ]
                                         , td_ [ text "50 ADA"
                                               ]
                                         ]
                                 ]
                        ]
