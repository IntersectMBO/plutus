module Simulation where

import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Ord ((>=))
import Marlowe.Semantics
import Data.Semiring ((+))
import Data.Map (Map)
import Data.List (List(..))
import Data.Set as Set
import API (RunResult(RunResult))
import Ace.Halogen.Component (Autocomplete(Live), aceComponent)
import Ace.Types (Editor)
import Bootstrap
  ( btn
  , btnInfo
  , btnPrimary
  , btnSmall
  , cardBody_
  , card
  , card_
  , col6
  , col_
  , row_
  , empty
  , listGroupItem_
  , listGroup_
  )
import Control.Alternative (map, (<|>))
import Effect.Aff.Class (class MonadAff)
import Effect (Effect)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Eq ((==), (/=))
import Data.Foldable (all)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Data.HeytingAlgebra ((&&))
import Halogen (HTML, action)
import Halogen.Component (ParentHTML)
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
  , li_
  , pre_
  , slot'
  , span
  , span_
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
  , ul_
  )
import Halogen.HTML.Events (input_, onChecked, onClick, onDragOver, onDrop, onValueChange)
import Halogen.HTML.Properties
  ( InputType
      ( InputCheckbox
      , InputNumber
      )
  , checked
  , class_
  , classes
  , enabled
  , placeholder
  , type_
  , value
  )
import Prelude
  ( Unit
  , bind
  , const
  , discard
  , flip
  , identity
  , pure
  , show
  , class Show
  , unit
  , void
  , ($)
  , (<$>)
  , (<<<)
  , (<>)
  )
import Marlowe.Types (BlockNumber(BlockNumber), Person, IdOracle, Choice, IdAction, IdCommit, Timeout, WIdChoice(..), IdChoice(..))
import Types
  ( ChildQuery
  , ChildSlot
  , FrontendState
  , InputData
  , MarloweEditorSlot
      ( MarloweEditorSlot
      )
  , MarloweError
      ( MarloweError
      )
  , MarloweState
  , OracleEntry
  , Query
      ( SetSignature
      , AddAnyInput
      , RemoveAnyInput
      , SetChoice
      , SetOracleVal
      , SetOracleBn
      , ResetSimulator
      , NextBlock
      , ApplyTransaction
      , LoadMarloweScript
      , MarloweHandleEditorMessage
      , MarloweHandleDropEvent
      , MarloweHandleDragEvent
      )
  , TransactionValidity(..)
  , cpMarloweEditor
  , isValidTransaction
  , isInvalidTransaction
  )

import Ace.EditSession as Session
import Ace.Editor as Editor
import Data.Array as Array
import Data.Map as Map
import Halogen.HTML.Events as Events
import Halogen.Query as HQ
import LocalStorage as LocalStorage
import StaticData as StaticData

paneHeader :: forall p. String -> HTML p Query
paneHeader s = h2 [class_ $ ClassName "pane-header"] [text s]

isContractValid :: FrontendState -> Boolean
isContractValid x = (x.marloweState.contract /= Nothing)

simulationPane ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ParentHTML Query ChildQuery ChildSlot m
simulationPane state =
  div_ (Array.concat [ [ row_ [ inputComposerPane state
                              , transactionComposerPane state
                              ]
                       , stateTitle state
                       , row_ [statePane state]
                       ]
                     , transErrors
                     , contractParsingErr
                     , [ div [ classes [ ClassName "demos"
                                       , ClassName "d-flex"
                                       , ClassName "flex-row"
                                       , ClassName "align-items-center"
                                       , ClassName "justify-content-between"
                                       , ClassName "mt-5"
                                       , ClassName "mb-3"
                                       ]
                             ] [paneHeader "Marlowe Contract", demoScriptsPane]
                       , div [ onDragOver $ Just <<< action <<< MarloweHandleDragEvent
                             , onDrop $ Just <<< action <<< MarloweHandleDropEvent
                             ] [ slot' cpMarloweEditor MarloweEditorSlot (aceComponent initEditor (Just Live)) unit (Events.input MarloweHandleEditorMessage)
                               ]
                       , br_
                       , errorList 
                       ]
                     ] )
  where
  transErrors = transactionErrors state.marloweState.transaction.validity
  contractParsingErr = contractParsingError (isContractValid state) 
  errorList = case state.marloweCompileResult of
    Left errors -> listGroup_ (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
    _ -> empty

loadBuffer :: Effect (Maybe String)
loadBuffer = LocalStorage.getItem StaticData.marloweBufferLocalStorageKey

initEditor ::
  forall m.
  MonadAff m =>
  Editor ->
  m Unit
initEditor editor = liftEffect $ do
  savedContents <- liftEffect loadBuffer
  let defaultContents = Map.lookup "Deposit Incentive" StaticData.marloweContracts
  let contents = fromMaybe "" (savedContents <|> defaultContents)
  void $ Editor.setValue contents (Just 1) editor
  Editor.setTheme "ace/theme/monokai" editor
  --
  --
  --
  --
  --
  --
  --
  --
  --
  session <- Editor.getSession editor
  Session.setMode "ace/mode/haskell" session

demoScriptsPane :: forall p. HTML p Query
demoScriptsPane = div_ (Array.cons (strong_ [ text "Demos: "
                                            ]) (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.marloweContracts)))

demoScriptButton :: forall p. String -> HTML p Query
demoScriptButton key = button [ classes [btn, btnInfo, btnSmall]
                              , onClick $ input_ $ LoadMarloweScript key
                              ] [text key]

compilationResultPane :: forall p. RunResult -> HTML p Query
compilationResultPane (RunResult stdout) = div_ [code_ [pre_ [text stdout]]]

compilationErrorPane :: forall p. MarloweError -> HTML p Query
compilationErrorPane (MarloweError error) = div_ [text error]

inputComposerPane :: forall p. FrontendState -> HTML p Query
inputComposerPane state = div [ classes [ col6
                                        , ClassName "input-composer"
                                        ]
                              ] [ paneHeader "Input Composer"
                                , div [ class_ $ ClassName "wallet"
                                      ] [ card_ [ cardBody_ (inputComposer isEnabled (state.marloweState.input))
                                                ]
                                        ]
                                ]
  where
    isEnabled = isContractValid state

onEmpty :: forall a. Array a -> Array a -> Array a
onEmpty alt [] = alt
onEmpty _ arr = arr

inputComposer :: forall p. Boolean -> InputData -> Array (HTML p Query)
inputComposer isEnabled { inputs, choiceData, oracleData } =
    onEmpty [ text "No valid inputs can be added to the transaction" ] $
    Array.concat [ Array.concat (Array.fromFoldable (map (\x -> inputComposerPerson isEnabled x inputs choiceData) people))
                 , if (Map.isEmpty oracleData)
                   then []
                   else [ h3_ [ text ("Oracles") ] ]
                 , Array.fromFoldable (map (inputComposerOracle isEnabled) oracles)
                 ]
  where
   ik = Set.fromFoldable (Map.keys inputs)
   cdk = Set.fromFoldable (Map.keys choiceData)
   people = Set.toUnfoldable (Set.union ik cdk) :: List Person
   oracles = Map.toUnfoldable oracleData :: List (Tuple IdOracle OracleEntry)

inputComposerPerson :: forall p. Boolean -> Person
                       -> Map Person (List DetachedPrimitiveWIA)
                       -> Map Person (Map BigInteger Choice)
                       -> Array (HTML p Query)
inputComposerPerson isEnabled person inputs choices =
  Array.concat
  [ [ h3_ [ text ("Person " <> show person)
          ] ]
  , case Map.lookup person inputs of
      Nothing -> []
      Just x -> do y <- Array.sortWith (idActionFromDWAI) (Array.fromFoldable x)
                   case y of
                     DWAICommit idAction idCommit val tim ->
                       pure (inputCommit isEnabled person idAction idCommit val tim)
                     DWAIPay idAction idCommit val ->
                       pure (inputPay isEnabled person idAction idCommit val)
  , case Map.lookup person choices of
      Nothing -> []
      Just x -> do (Tuple idChoice choice) <- Map.toUnfoldable x
                   pure (inputChoice isEnabled person idChoice choice)
  ]
  where
  idActionFromDWAI (DWAICommit idAction _ _ _) = idAction
  idActionFromDWAI (DWAIPay idAction _ _) = idAction

inputCommit :: forall p. Boolean -> Person -> IdAction -> IdCommit -> BigInteger -> Timeout
                -> HTML p Query
inputCommit isEnabled person idAction idCommit val tim =
  flexRow_ [ button [ class_ $ ClassName "composer-add-button" 
                    , enabled isEnabled
                    , onClick $ input_ $ AddAnyInput { person: Just person
                                                     , anyInput: Action idAction }
                    ] [ text "+"
                      ]
           , spanText "Action "
           , b_ [ spanText (show idAction) ]
           , spanText ": Commit "
           , b_ [ spanText (show val) ]
           , spanText " ADA with id "
           , b_ [ spanText (show idCommit) ]
           , spanText " to expire by "
           , b_ [ spanText (show tim) ]
           ]

inputPay :: forall p. Boolean -> Person -> IdAction -> IdCommit -> BigInteger -> HTML p Query
inputPay isEnabled person idAction idCommit val =
  flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                    , enabled isEnabled
                    , onClick $ input_ $ AddAnyInput { person: Just person
                                                     , anyInput: Action idAction }
                    ] [ text "+"
                      ]
           , spanText "Action "
           , b_ [ spanText (show idAction) ]
           , spanText ": Claim "
           , b_ [ spanText (show val) ]
           , spanText " ADA from commit "
           , b_ [ spanText (show idCommit) ]
           ]

inputChoice :: forall p. Boolean -> Person -> BigInteger -> BigInteger -> HTML p Query
inputChoice isEnabled person idChoice val =
  flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                    , enabled isEnabled
                    , onClick $ input_ $ AddAnyInput { person: Just person
                                                     , anyInput: Input (IChoice (IdChoice {choice: idChoice, person}) val) }
                    ] [ text "+"
                      ]
           , spanText "Choice "
           , b_ [ spanText (show idChoice) ]
           , spanText ": Choose value "
           , marloweActionInput isEnabled
                                (\x -> SetChoice { idChoice: (IdChoice {choice: idChoice
                                                                       , person})
                                                 , value: x}) val
           ]

inputComposerOracle :: forall p. Boolean -> Tuple IdOracle OracleEntry -> HTML p Query
inputComposerOracle isEnabled (Tuple idOracle {blockNumber, value}) =
  flexRow_ [ button [ class_ $ ClassName "composer-add-button"
                    , enabled isEnabled
                    , onClick $ input_ $ AddAnyInput { person: Nothing
                                                     , anyInput: Input (IOracle idOracle blockNumber value) }
                    ] [ text "+"
                      ]
           , spanText "Oracle "
           , b_ [ spanText (show idOracle) ]
           , spanText ": Provide "
           , marloweActionInput isEnabled
                                (\x -> SetOracleVal { idOracle
                                                    , value: x}) value
           , spanText " as the value for block "
           , marloweActionInput isEnabled
                                (\x -> SetOracleBn { idOracle
                                                   , blockNumber: BlockNumber (unwrap x)}) blockNumber
           ]

marloweActionInput :: forall p a. Show a => Boolean -> (BigInteger -> Unit -> Query Unit) -> a -> HTML p Query
marloweActionInput isEnabled f current =
  input [ type_ InputNumber
        , enabled isEnabled
        , placeholder "BigInteger"
        , class_ $ ClassName "action-input"
        , value $ show current
        , onValueChange $ (\x -> Just $ HQ.action $ f (case fromString x of
                                                        Just y -> y
                                                        Nothing -> fromInt 0))
        ]


flexRow_ ::
  forall p.
  Array (HTML p Query) ->
  HTML p Query
flexRow_ html = div [classes [ClassName "d-flex", ClassName "flex-row"]] html

spanText :: forall p. String -> HTML p Query
spanText s = span [class_ $ ClassName "pr-1"] [text s]

transactionComposerPane ::
  forall p.
  FrontendState ->
  HTML p Query
transactionComposerPane state =
        div [ classes [ col6
                      , ClassName "input-composer"
                      ]
            ] [ paneHeader "Transaction Composer"
              , div [ class_ $ ClassName "wallet"
                    ] [ div [ classes ((if (isInvalidTransaction state.marloweState.transaction.validity)
                                        then (flip Array.snoc) (ClassName "invalid-transaction")
                                        else identity) [card]) ]
                            [ cardBody_ $ transactionInputs state.marloweState
                               <> (signatures state.marloweState.transaction.signatures
                                   (isContractValid state)
                                   state.marloweState.transaction.outcomes)
                               <> transactionButtons state
                            ]
                      ]
              ]

transactionButtons :: FrontendState -> forall p. Array (HTML p Query)
transactionButtons state = [ div [ classes [ ClassName "d-flex"
                                           , ClassName "flex-row"
                                           , ClassName "align-items-center"
                                           , ClassName "justify-content-start"
                                           , ClassName "transaction-btn-row"
                                           ]
                                 ] [ button [ classes [ btn
                                                      , btnPrimary
                                                      , ClassName "transaction-btn"
                                                      ]
                                            , onClick $ Just <<< HQ.action <<< const ApplyTransaction
                                            , enabled (isValidTransaction state.marloweState.transaction.validity && isContractValid state)
                                            ] [text "Apply Transaction"]
                                   , button [ classes [ btn
                                                      , btnPrimary
                                                      , ClassName "transaction-btn"
                                                      ]
                                            , onClick $ Just <<< HQ.action <<< const NextBlock
                                            , enabled (isContractValid state)
                                            ] [text "Next Block"]
                                   , button [ classes [ btn
                                                      , btnPrimary
                                                      , ClassName "transaction-btn"
                                                      ]
                                            , enabled (state.oldContract /= Nothing)
                                            , onClick $ Just <<< HQ.action <<< const ResetSimulator
                                            ] [text "Reset"]
                                   ]
                           ]

printTransWarnings :: forall p. Int -> List DynamicProblem -> Array (HTML p Query)
printTransWarnings _ Nil = []
printTransWarnings num (Cons NoProblem rest) = printTransWarnings (num + 1) rest
printTransWarnings num (Cons CommitNotMade rest) =
  Array.cons (text ("Input number " <> (show num) <> " will have no effect because the commitment has not been made yet."))
             (printTransWarnings (num + 1) rest)
printTransWarnings num (Cons NotEnoughMoneyLeftInCommit rest) =
  Array.cons (text ("Input number " <> (show num) <> " will not have the expected effect because there is not enough money left in the commit."))
             (printTransWarnings (num + 1) rest)
printTransWarnings num (Cons CommitIsExpired rest) =
  Array.cons (text ("Input number " <> (show num) <> " will have no effect because the commitment has expired already."))
             (printTransWarnings (num + 1) rest)

printTransError :: forall p. ErrorResult -> Array (HTML p Query)
printTransError InvalidInput = [ul_ [li_ [text "At least one of the inputs in the transaction is not acceptable given the state of the contract."]]]
printTransError NoValidSignature = [ul_ [li_ [text "At least one of the inputs requires a signature that is not provided."]]]
printTransError NegativeTransaction = [ul_ [li_ [text "At least one of transactions is for a negative amount of money."]]]
printTransError AmbiguousId = [ul_ [li_ [text "At least one of the action identifiers appears more than once in the contract. Please, ensure that every contruct in the contract has a unique id."]]]
printTransError InternalError = [ul_ [li_ [text "The internal state of the contract is inconsistent. This should not happen. Please, open an issue and let us know how you got to this error."]]]

contractParsingError :: forall p. Boolean -> Array (HTML p Query)
contractParsingError true = [div [classes [ ClassName "invalid-transaction"
                                           , ClassName "input-composer"
                                           ]
                                  ]
                                  [ h2 [] [text ""]
                                  ]
                             ]
contractParsingError false = [div [classes [ ClassName "invalid-transaction"
                                           , ClassName "input-composer"
                                           ]
                                  ]
                                  [ h2 [] [text "Cannot parse contract"]
                                  ]
                             ]
 
transactionErrors :: forall p. TransactionValidity -> Array (HTML p Query)
transactionErrors EmptyTransaction = []
transactionErrors (ValidTransaction l) = if (all (\x -> x == NoProblem) l)
                                         then [] 
                                         else [div [classes [ ClassName "warning-transaction"
                                                            , ClassName "input-composer"
                                                            ]
                                                   ]
                                                   [ h2 [] [text "Transaction is valid but:"]
                                                   , transWarn 
                                                   ]
                                              ]
  where
  transWarn = ul_ (map (li_ <<< pure) (printTransWarnings 1 l)) 
transactionErrors (InvalidTransaction err) = [div [classes [ ClassName "invalid-transaction"
                                                           , ClassName "input-composer"
                                                           ]
                                                  ]
                                                  ([ h2 [] [text "The transaction is invalid:"]]
                                                   <> printTransError err)]

signatures :: forall p. Map Person Boolean -> Boolean -> Map Person BigInteger -> Array (HTML p Query)
signatures people isEnabled outcomes =
  [ h3_ [text "Signatures"]
  , if ((Map.size people) == 0)
    then div [] [text "No participants in contract"]
    else div [ classes [ ClassName "d-flex"
                       , ClassName "flex-row"
                       , ClassName "align-items-center"
                       , ClassName "justify-content-start"
                       ]
             ] (map (\x -> signature x isEnabled outcomes) $ Map.toUnfoldable people)
  ]

signature :: forall p. Tuple Person Boolean -> Boolean -> Map Person BigInteger -> HTML p Query
signature (Tuple person isChecked) isEnabled outcomes =
  span [ class_ $ ClassName "pr-2"
       ] [ input [ type_ InputCheckbox
                 , onChecked $ Just <<< HQ.action <<< (\v -> SetSignature { person
                                                                          , isChecked: v
                                                                          })
                 , enabled isEnabled 
                 , checked isChecked
                 ]
         , span_ [ text $ " Person " <> show person
                 ]
         , span  [ classes [ ClassName "outcome-block" ] ]
                 [ text $ "(" <> outcome <> " ADA)"
                 ]
         ]
  where outcome = case Map.lookup person outcomes of
                    Nothing -> "+0"
                    Just x -> if (x >= fromInt 0) then "+" <> show x else show x

transactionInputs :: forall p. MarloweState -> Array (HTML p Query)
transactionInputs state = [ h3_ [ text "Input list"
                                ]
                          ] <> ( onEmpty [ text "No inputs in the transaction" ] $
                                 map (inputRow isEnabled) state.transaction.inputs )
  where
    isEnabled = state.contract /= Nothing 

inputRow :: forall p. Boolean -> AnyInput -> HTML p Query
inputRow isEnabled idInput@(Action idAction) =
  row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                       , enabled isEnabled
                       , onClick $ input_ $ RemoveAnyInput idInput
                       ] [ text "-"
                         ]
              , text "Action with id "
              , b_ [ text (show idAction)
                   ]
              ]
       ]

inputRow isEnabled idInput@(Input (IChoice (IdChoice {choice, person}) val)) =
  row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                       , enabled isEnabled
                       , onClick $ input_ $ RemoveAnyInput idInput
                       ] [ text "-"
                         ]
              , text "Participant "
              , b_ [ text (show person)
                   ]
              , text " chooses the value "
              , b_ [ text (show val)
                   ]
              , text " for choice with id "
              , b_ [ text (show choice)
                   ]
              ]
       ]

inputRow isEnabled idInput@(Input (IOracle idOracle bn val)) =
  row_ [ col_ [ button [ class_ $ ClassName "composer-add-button"
                       , enabled isEnabled
                       , onClick $ input_ $ RemoveAnyInput idInput
                       ] [ text "-"
                         ]
              , text "Oracle "
              , b_ [ text (show idOracle)
                   ]
              , text " had value "
              , b_ [ text (show val)
                   ]
              , text " at block "
              , b_ [ text (show bn)
                   ]
              ]
       ]

stateTitle ::
  forall p.
  FrontendState ->
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
                                         ] [ text (show state.marloweState.blockNum)
                                           ]
                                  , strong_ [ text "Money in contract:"
                                            ]
                                  , span [ class_ $ ClassName "money-in-contract"
                                         ] [ text (show state.marloweState.moneyInContract)
                                           ]
                                  , strong_ [ text "ADA" ]
                                  ]
                         ]

statePane :: forall p. FrontendState -> HTML p Query
statePane state = div [ class_ $ ClassName "col"
                      ] [ stateTable state
                        ]

stateTable :: forall p. FrontendState -> HTML p Query
stateTable state =
  div [ class_ $ ClassName "full-width-card"
      ] [ card_ [ cardBody_
                    [ h3_ [ text "Money owed"
                          ]
                    , row_ [ if (Map.size commits.redeemedPerPerson == 0)
                             then text "No participant is owed money"
                             else renderMoneyOwed mState.commits
                           ]
                    , h3_ [ text "Commits"
                          ]
                    , row_ [ if (Map.size commits.currentCommitsById == 0)
                             then text "There are no commits in the state"
                             else renderCommits mState.commits
                           ]
                    , h3_ [ text "Choices"
                          ]
                    , row_ [ if (Map.size mState.choices == 0)
                             then text "No choices have been recorded"
                             else renderChoices mState.choices
                           ]
                    , h3_ [ text "Oracle values"
                          ]
                    , row_ [ if (Map.size mState.oracles == 0)
                             then text "No oracle values have been recorded"
                             else renderOracles mState.oracles
                           ]
                    ]
                ]
        ]
  where (State mState) = state.marloweState.state
        (CommitInfo commits) = mState.commits

renderMoneyOwed :: forall p. CommitInfo -> HTML p Query
renderMoneyOwed (CommitInfo ci) =
  table_ [ colgroup [] [ col []
                       , col []
                       ]
         , thead_ [ tr [] [ th_ [ text "Participant id"
                                ]
                          , th [ class_ $ ClassName "left-border-column"
                               ] [ text "Owed amount"
                                 ]
                          ]
                  ]
         , tbody_ (Array.fromFoldable (map renderMoneyOwedIndividual owedList))
         ]
  where owedList = Map.toUnfoldable ci.redeemedPerPerson :: List (Tuple Person BigInteger)

renderMoneyOwedIndividual :: forall p. Tuple Person BigInteger -> HTML p Query
renderMoneyOwedIndividual (Tuple person amount) =
  tr [] [ td_ [ text (show person)
              ]
        , td_ [ text (show amount <> " ADA")
              ]
        ]

renderCommits :: forall p. CommitInfo -> HTML p Query
renderCommits (CommitInfo ci) =
  table_ [ colgroup [] [ col []
                       , col []
                       , col []
                       , col []
                       ]
         , thead_ [ tr [] [ th_ [ text "Commit id"
                                ]
                          , th [ class_ $ ClassName "middle-column"
                               ] [ text "Owner"
                                 ]
                          , th [ class_ $ ClassName "middle-column"
                               ] [ text "Amount"
                                 ]
                          , th_ [ text "Expiration"
                                ]
                          ]
                  ]
         , tbody_ (Array.fromFoldable (map renderCommit commitList))
         ]
  where commitList = Map.toUnfoldable ci.currentCommitsById :: List (Tuple IdCommit CommitInfoRecord)

renderCommit :: forall p. Tuple IdCommit CommitInfoRecord -> HTML p Query
renderCommit (Tuple idCommit (CommitInfoRecord {person, amount, timeout})) =
  tr [] [ td_ [ text (show idCommit)
              ]
        , td [ class_ $ ClassName "middle-column"
             ] [ text (show person)
               ]
        , td [ class_ $ ClassName "middle-column"
             ] [ text (show amount <> " ADA")
               ]
        , td_ [ text (show timeout)
              ]
        ]

renderChoices :: forall p. Map WIdChoice Choice -> HTML p Query
renderChoices choices =
  table_ [ colgroup [] [ col []
                       , col []
                       , col []
                       ]
         , thead_ [ tr [] [ th_ [ text "Choice id"
                                ]
                          , th [ class_ $ ClassName "middle-column"
                               ] [ text "Participant"
                                 ]
                          , th_ [ text "Chosen value"
                                ]
                          ]
                  ]
         , tbody_ (Array.fromFoldable (map renderChoice choiceList))
         ]
  where choiceList = Map.toUnfoldable choices :: List (Tuple WIdChoice Choice)

renderChoice :: forall p. Tuple WIdChoice Choice -> HTML p Query
renderChoice (Tuple (WIdChoice (IdChoice {choice, person})) value) =
  tr [] [ td_ [ text (show choice)
              ]
        , td [ class_ $ ClassName "middle-column"
             ] [ text (show person)
               ]
        , td_ [ text (show value)
              ]
        ]

renderOracles :: forall p. Map IdOracle OracleDataPoint -> HTML p Query
renderOracles oracles =
  table_ [ colgroup [] [ col []
                       , col []
                       , col []
                       ]
         , thead_ [ tr [] [ th_ [ text "Oracle id"
                                ]
                          , th [ class_ $ ClassName "middle-column"
                               ] [ text "Timestamp"
                                 ]
                          , th_ [ text "Value"
                                ]
                          ]
                  ]
         , tbody_ (Array.fromFoldable (map renderOracle oracleList))
         ]
  where oracleList = Map.toUnfoldable oracles :: List (Tuple IdOracle OracleDataPoint)

renderOracle :: forall p. Tuple IdOracle OracleDataPoint -> HTML p Query
renderOracle (Tuple idOracle (OracleDataPoint {blockNumber, value})) =
  tr [] [ td_ [ text (show idOracle)
              ]
        , td [ class_ $ ClassName "middle-column"
             ] [ text (show blockNumber)
               ]
        , td_ [ text (show value)
              ]
        ]
