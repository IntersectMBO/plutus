module Simulation where

import API (RunResult(RunResult))
import Ace.Halogen.Component (Autocomplete(Live), aceComponent)
import Ace.Types as Ace
import Bootstrap (btn, btnInfo, btnPrimary, btnSecondary, btnSmall, card, cardBody_, card_, col3_, col6, col9, col_, dropdownToggle, empty, listGroupItem_, listGroup_, row_)
import Bootstrap.Extra (ariaExpanded, ariaHasPopup, ariaLabelledBy, dataToggle)
import Control.Alternative (map)
import Data.Array (catMaybes, concatMap, fromFoldable, head, sortBy)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Either (Either(..))
import Data.Eq ((==), (/=))
import Data.Foldable (foldMap, intercalate)
import Data.Function (on)
import Data.FunctorWithIndex (mapWithIndex)
import Data.HeytingAlgebra ((&&), (||))
import Data.Lens (to, view, (^.))
import Data.List (List, toUnfoldable, null)
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Tuple (Tuple(..), snd)
import Editor (initEditor) as Editor
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, PropName(..), a, b_, br_, button, code_, col, colgroup, div, div_, h2, h3_, input, li_, ol, ol_, pre_, slot, span, span_, strong_, table_, tbody_, td, td_, text, th, th_, thead_, tr, ul_)
import Halogen.HTML.Events (onClick, onDragOver, onDrop, onValueChange)
import Halogen.HTML.Properties (ButtonType(..), InputType(InputNumber), class_, classes, enabled, id_, placeholder, prop, type_, value)
import Halogen.HTML.Properties.ARIA (role)
import Marlowe.Holes (Holes(..), MarloweHole(..), MarloweType(..), getMarloweConstructors)
import Marlowe.Parser (transactionInputList, transactionWarningList)
import Marlowe.Semantics (AccountId(..), Assets(..), Bound(..), ChoiceId(..), ChosenNum, CurrencySymbol, Input(..), Party, Payee(..), Payment(..), PubKey, Slot(..), SlotInterval(..), Token(..), TokenName, TransactionError, TransactionInput(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, inBounds, maxTime)
import Marlowe.Symbolic.Types.Response as R
import Network.RemoteData (RemoteData(..), isLoading)
import Prelude (class Show, bind, compare, const, flip, identity, mempty, not, pure, show, unit, zero, ($), (+), (<$>), (<<<), (<>), (>))
import StaticData as StaticData
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Types (ActionInput(..), ActionInputId, ChildSlots, FrontendState, HAction(..), MarloweError(..), MarloweState, _Head, _analysisState, _contract, _editorErrors, _editorPreferences, _holes, _marloweCompileResult, _marloweEditorSlot, _marloweState, _payments, _pendingInputs, _possibleActions, _selectedHole, _slot, _state, _transactionError, _transactionWarnings)

paneHeader :: forall p. String -> HTML p HAction
paneHeader s = h2 [ class_ $ ClassName "pane-header" ] [ text s ]

isContractValid :: FrontendState -> Boolean
isContractValid state =
  view (_marloweState <<< _Head <<< _contract) state /= Nothing
    && view (_marloweState <<< _Head <<< _editorErrors) state
    == []

simulationPane ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML HAction ChildSlots m
simulationPane state =
  div_
    ( Array.concat
        [ [ row_
              [ inputComposerPane state
              , transactionComposerPane state
              ]
          , row_ [ displayWarnings warnings ]
          , row_ [ col_ (state ^. (_marloweState <<< _Head <<< _transactionError <<< to transactionErrors)) ]
          , stateTitle state
          , row_ [ statePane state ]
          ]
        , [ div
              [ classes
                  [ ClassName "demos"
                  , ClassName "d-flex"
                  , ClassName "flex-row"
                  , ClassName "align-items-center"
                  , ClassName "justify-content-between"
                  , ClassName "mt-5"
                  , ClassName "mb-3"
                  ]
              ]
              [ paneHeader "Marlowe Contract", codeToBlocklyButton state, demoScriptsPane ]
          , div
              [ onDragOver $ Just <<< MarloweHandleDragEvent
              , onDrop $ Just <<< MarloweHandleDropEvent
              ]
              [ row_
                  [ div [ class_ col9 ] [ slot _marloweEditorSlot unit marloweEditor unit (Just <<< MarloweHandleEditorMessage) ]
                  , holesPane (view _selectedHole state) (view (_marloweState <<< _Head <<< _holes) $ state)
                  ]
              ]
          , br_
          , errorList
          , analysisPane state
          ]
        ]
    )
  where
  marloweEditor =
    aceComponent (Editor.initEditor initialContents StaticData.marloweBufferLocalStorageKey editorPreferences)
      (Just Live)

  editorPreferences = view _editorPreferences state

  initialContents = Map.lookup "Deposit Incentive" StaticData.marloweContracts

  errorList = case view _marloweCompileResult state of
    Left errors -> listGroup_ (listGroupItem_ <<< pure <<< compilationErrorPane <$> errors)
    _ -> empty

  warnings = view (_marloweState <<< _Head <<< _transactionWarnings) state

holesPane :: forall p. Maybe String -> Holes -> HTML p HAction
holesPane selectedHole (Holes holes) =
  let
    kvs = Map.toUnfoldable holes

    ordered = sortBy sortHoles kvs

    holesGroup = map (\(Tuple k v) -> displayHole selectedHole k v) ordered
  in
    col3_
      [ div
          [ class_ $ ClassName "btn-group-vertical"
          , role "group"
          ]
          holesGroup
      ]
  where
  sortHoles = compare `on` (head <<< snd)

displayHole :: forall p. Maybe String -> String -> Array MarloweHole -> HTML p HAction
displayHole selectedHole name holes =
  div [ classes ([ ClassName "btn-group" ] <> showClass) ]
    [ button
        [ classes [ btn, btnSecondary, dropdownToggle, ClassName "button-box" ]
        , id_ ("hole-btn-" <> name)
        , type_ ButtonButton
        , dataToggle "dropdown"
        , ariaHasPopup true
        , ariaExpanded expanded
        , onClick $ const $ Just $ SelectHole selectHole
        ]
        [ text name ]
    , div
        [ classes ([ ClassName "dropdown-menu" ] <> showClass)
        , ariaLabelledBy ("hole-btn-" <> name)
        ]
        (holeDropdowns holes)
    ]
  where
  expanded = selectedHole == Just name

  showClass = if selectedHole == Just name then [ ClassName "show" ] else []

  selectHole = if selectedHole == Just name then Nothing else Just name

holeDropdowns :: forall p. Array MarloweHole -> Array (HTML p HAction)
holeDropdowns holes = case Array.uncons holes of
  Nothing -> mempty
  Just { head: (MarloweHole { marloweType: BigIntegerType, end }) } ->
    [ div
        [ classes [ ClassName "dropdown-item", ClassName "font-italic" ]
        , onClick $ const $ Just $ MarloweMoveToPosition $ holeToAcePosition end
        ]
        [ text "Replace the hole with an integer" ]
    ]
  Just { head: (MarloweHole { marloweType: StringType, end }) } ->
    [ div
        [ classes [ ClassName "dropdown-item", ClassName "font-italic" ]
        , onClick $ const $ Just $ MarloweMoveToPosition $ holeToAcePosition end
        ]
        [ text "Replace the hole with a string" ]
    ]
  Just { head: (MarloweHole { marloweType: ValueIdType, end }) } ->
    [ div
        [ classes [ ClassName "dropdown-item", ClassName "font-italic" ]
        , onClick $ const $ Just $ MarloweMoveToPosition $ holeToAcePosition end
        ]
        [ text "Replace the hole with a string" ]
    ]
  Just { head: (MarloweHole { marloweType: SlotType, end }) } ->
    [ div
        [ classes [ ClassName "dropdown-item", ClassName "font-italic" ]
        , onClick $ const $ Just $ MarloweMoveToPosition $ holeToAcePosition end
        ]
        [ text "Replace the hole with an integer" ]
    ]
  Just { head: hole@(MarloweHole { marloweType }) } ->
    map
      ( \constructor ->
          a
            [ class_ $ ClassName "dropdown-item"
            , onClick $ const $ Just $ InsertHole constructor hole holes
            ]
            [ text constructor ]
      )
      (fromFoldable $ Map.keys $ getMarloweConstructors marloweType)
  where
  holeToAcePosition (Position { column, line }) = Ace.Position { column, row: line }

demoScriptsPane :: forall p. HTML p HAction
demoScriptsPane =
  div_
    ( Array.cons
        ( strong_
            [ text "Demos: "
            ]
        )
        (demoScriptButton <$> Array.fromFoldable (Map.keys StaticData.marloweContracts))
    )

demoScriptButton :: forall p. String -> HTML p HAction
demoScriptButton key =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ const $ Just $ LoadMarloweScript key
    ]
    [ text key ]

codeToBlocklyButton :: forall p. FrontendState -> HTML p HAction
codeToBlocklyButton state =
  button
    [ classes [ btn, btnInfo, btnSmall ]
    , onClick $ const $ Just $ SetBlocklyCode
    , enabled (isContractValid state)
    ]
    [ text "Code to Blockly" ]

compilationResultPane :: forall p. RunResult -> HTML p HAction
compilationResultPane (RunResult stdout) = div_ [ code_ [ pre_ [ text stdout ] ] ]

compilationErrorPane :: forall p. MarloweError -> HTML p HAction
compilationErrorPane (MarloweError error) = div_ [ text error ]

inputComposerPane :: forall p. FrontendState -> HTML p HAction
inputComposerPane state =
  div
    [ classes
        [ col6
        , ClassName "input-composer"
        ]
    ]
    [ paneHeader "Input Composer"
    , div
        [ class_ $ ClassName "wallet"
        ]
        [ card_
            [ cardBody_ (inputComposer isEnabled (view (_marloweState <<< _Head <<< _possibleActions) state))
            ]
        ]
    ]
  where
  isEnabled = isContractValid state

onEmpty :: forall a. Array a -> Array a -> Array a
onEmpty alt [] = alt

onEmpty _ arr = arr

inputComposer :: forall p. Boolean -> Map (Maybe PubKey) (Map ActionInputId ActionInput) -> Array (HTML p HAction)
inputComposer isEnabled actionInputs =
  if (Map.isEmpty actionInputs) then
    [ text "No valid inputs can be added to the transaction" ]
  else
    (actionsForPeople actionInputs)
  where
  kvs :: forall k v. Map k v -> Array (Tuple k v)
  kvs = Map.toUnfoldable

  vs :: forall k v. Map k v -> Array v
  vs m = map snd (kvs m)

  lastKey :: Maybe (Maybe PubKey)
  lastKey = map (\x -> x.key) (Map.findMax actionInputs)

  actionsForPeople :: forall q. Map (Maybe PubKey) (Map ActionInputId ActionInput) -> Array (HTML q HAction)
  actionsForPeople m = foldMap (\(Tuple k v) -> inputComposerPerson isEnabled k (vs v) (Just k == lastKey)) (kvs m)

inputComposerPerson ::
  forall p.
  Boolean ->
  Maybe PubKey ->
  Array ActionInput ->
  Boolean ->
  Array (HTML p HAction)
inputComposerPerson isEnabled maybePerson actionInputs isLast =
  [ h3_
      [ text
          ( case maybePerson of
              Just person -> ("Participant " <> show person)
              Nothing -> ("Anyone")
          )
      ]
  ]
    <> [ div [ class_ $ ClassName (if isLast then "state-last-row" else "state-row") ]
          (catMaybes (mapWithIndex inputForAction actionInputs))
      ]
  where
  inputForAction :: Int -> ActionInput -> Maybe (HTML p HAction)
  inputForAction index (DepositInput accountId party token value) = Just $ inputDeposit isEnabled maybePerson index accountId party token value

  inputForAction index (ChoiceInput choiceId bounds chosenNum) = Just $ inputChoice isEnabled maybePerson index choiceId chosenNum bounds

  inputForAction index NotifyInput = Just $ inputNotify isEnabled maybePerson index

inputDeposit ::
  forall p.
  Boolean ->
  Maybe PubKey ->
  Int ->
  AccountId ->
  Party ->
  Token ->
  BigInteger ->
  HTML p HAction
inputDeposit isEnabled person index accountId party token value =
  flexRow_
    $ [ button
          [ class_ $ ClassName "composer-add-button"
          , enabled isEnabled
          , onClick $ const $ Just
              $ AddInput person (IDeposit accountId party token value) []
          ]
          [ text "+"
          ]
      ]
    <> (renderDeposit accountId party token value)

renderDeposit :: forall p. AccountId -> Party -> Token -> BigInteger -> Array (HTML p HAction)
renderDeposit (AccountId accountNumber accountOwner) party tok money =
  [ spanText "Deposit "
  , b_ [ spanText (show money) ]
  , spanText " units of "
  , b_ [ spanText (show tok) ]
  , spanText " into Account "
  , b_ [ spanText (show accountOwner <> " (" <> show accountNumber <> ")") ]
  , spanText " as "
  , b_ [ spanText party ]
  ]

inputChoice :: forall p. Boolean -> Maybe PubKey -> Int -> ChoiceId -> ChosenNum -> Array Bound -> HTML p HAction
inputChoice isEnabled person index choiceId@(ChoiceId choiceName choiceOwner) chosenNum bounds =
  let
    validBounds = inBounds chosenNum bounds

    errorRow = if validBounds then [] else [ text boundsError ]
  in
    flexRow_
      ( [ button
            [ class_ $ ClassName "composer-add-button"
            , enabled isEnabled
            , onClick $ const $ Just
                $ AddInput person (IChoice (ChoiceId choiceName choiceOwner) chosenNum) bounds
            ]
            [ text "+"
            ]
        , spanText "Choice "
        , b_ [ spanText (show choiceName) ]
        , spanText ": Choose value "
        , marloweActionInput isEnabled (SetChoice choiceId) chosenNum
        ]
          <> errorRow
      )
  where
  boundsError = "Choice must be between " <> intercalate " or " (map boundError bounds)

  boundError (Bound from to) = show from <> " and " <> show to

inputNotify ::
  forall p.
  Boolean ->
  Maybe PubKey ->
  Int ->
  HTML p HAction
inputNotify isEnabled person index =
  flexRow_
    [ button
        [ class_ $ ClassName "composer-add-button"
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput person INotify []
        ]
        [ text "+"
        ]
    , text $ "Notify contract"
    ]

marloweActionInput :: forall p a. Show a => Boolean -> (BigInteger -> HAction) -> a -> HTML p HAction
marloweActionInput isEnabled f current =
  input
    [ type_ InputNumber
    , enabled isEnabled
    , placeholder "BigInteger"
    , class_ $ ClassName "action-input"
    , value $ show current
    , onValueChange
        $ ( \x ->
              Just
                $ f
                    ( case fromString x of
                        Just y -> y
                        Nothing -> fromInt 0
                    )
          )
    ]

flexRow_ ::
  forall p.
  Array (HTML p HAction) ->
  HTML p HAction
flexRow_ html = div [ classes [ ClassName "d-flex", ClassName "flex-row" ] ] html

spanText :: forall p. String -> HTML p HAction
spanText s = span [ class_ $ ClassName "pr-1" ] [ text s ]

transactionComposerPane ::
  forall p.
  FrontendState ->
  HTML p HAction
transactionComposerPane state =
  div
    [ classes
        [ col6
        , ClassName "input-composer"
        ]
    ]
    [ paneHeader "Transaction Composer"
    , div
        [ class_ $ ClassName "wallet"
        ]
        [ div
            [ classes
                ( ( if view (_marloweState <<< _Head <<< _transactionError <<< to isJust) state then
                      (flip Array.snoc) (ClassName "invalid-transaction")
                    else
                      identity
                  )
                    [ card ]
                )
            ]
            [ cardBody_
                $ transactionInputs (view (_marloweState <<< _Head) state)
                <> transactionButtons state
            ]
        ]
    ]

transactionButtons :: FrontendState -> forall p. Array (HTML p HAction)
transactionButtons state =
  [ div
      [ classes
          [ ClassName "d-flex"
          , ClassName "flex-row"
          , ClassName "align-items-center"
          , ClassName "justify-content-start"
          , ClassName "transaction-btn-row"
          ]
      ]
      [ button
          [ classes
              [ btn
              , btnPrimary
              , ClassName "transaction-btn"
              ]
          , onClick $ Just <<< const ApplyTransaction
          , enabled $ isContractValid state
          ]
          [ text "Apply Transaction" ]
      , button
          [ classes
              [ btn
              , btnPrimary
              , ClassName "transaction-btn"
              ]
          , onClick $ Just <<< const NextSlot
          , enabled (isContractValid state)
          ]
          [ text "Next Block" ]
      , button
          [ classes
              [ btn
              , btnPrimary
              , ClassName "transaction-btn"
              ]
          , enabled (hasHistory state)
          , onClick $ Just <<< const ResetSimulator
          ]
          [ text "Reset" ]
      , button
          [ classes
              [ btn
              , btnPrimary
              , ClassName "transaction-btn"
              ]
          , enabled (hasHistory state)
          , onClick $ Just <<< const Undo
          ]
          [ text "Undo" ]
      ]
  ]

hasHistory :: FrontendState -> Boolean
hasHistory state = NEL.length (view _marloweState state) > 1

-- TODO: Need to make these errors nice explanations - function in smeantics utils
printTransError :: forall p. TransactionError -> Array (HTML p HAction)
printTransError error = [ ul_ [ li_ [ text (show error) ] ] ]

transactionErrors :: forall p. Maybe TransactionError -> Array (HTML p HAction)
transactionErrors Nothing = []

transactionErrors (Just error) =
  [ div
      [ classes
          [ ClassName "invalid-transaction"
          , ClassName "input-composer"
          ]
      ]
      ( [ h2 [] [ text "The transaction is invalid:" ] ]
          <> printTransError error
      )
  ]

transactionInputs :: forall p. MarloweState -> Array (HTML p HAction)
transactionInputs state =
  [ h3_
      [ text "Input list"
      ]
  ]
    <> [ div [ class_ $ ClassName "state-row" ]
          ( onEmpty [ text "No inputs in the transaction" ]
              $ mapWithOneIndex (inputRow isEnabled) (state ^. _pendingInputs)
          )
      ]
  where
  isEnabled = state.contract /= Nothing || state.editorErrors /= []

  mapWithOneIndex f = mapWithIndex (\i a -> f (i + 1) a)

inputRow :: forall p. Boolean -> Int -> Tuple Input (Maybe PubKey) -> HTML p HAction
inputRow isEnabled idx (Tuple INotify person) =
  row_
    [ col_
        [ button
            [ class_ $ ClassName "composer-add-button"
            , enabled isEnabled
            , onClick $ const $ Just $ RemoveInput person INotify
            ]
            [ text $ "- " <> show idx <> ":"
            ]
        , text "Notification"
        ]
    ]

inputRow isEnabled idx (Tuple input@(IDeposit accountId party token money) person) =
  row_
    [ col_
        $ [ button
              [ class_ $ ClassName "composer-add-button"
              , enabled isEnabled
              , onClick $ const $ Just $ RemoveInput person input
              ]
              [ text $ "- " <> show idx <> ":"
              ]
          ]
        <> (renderDeposit accountId party token money)
    ]

inputRow isEnabled idx (Tuple input@(IChoice (ChoiceId choiceName choiceOwner) chosenNum) person) =
  row_
    [ col_
        [ button
            [ class_ $ ClassName "composer-add-button"
            , enabled isEnabled
            , onClick $ const $ Just $ RemoveInput person input
            ]
            [ text $ "- " <> show idx <> ":"
            ]
        , text "Participant "
        , b_
            [ text (show choiceOwner)
            ]
        , text " chooses the value "
        , b_
            [ text (show chosenNum)
            ]
        , text " for choice with id "
        , b_
            [ text (show choiceName)
            ]
        ]
    ]

stateTitle ::
  forall p.
  FrontendState ->
  HTML p HAction
stateTitle state =
  div
    [ classes
        [ ClassName "demos"
        , ClassName "d-flex"
        , ClassName "flex-row"
        , ClassName "align-items-center"
        , ClassName "justify-content-between"
        , ClassName "mt-3"
        , ClassName "mb-3"
        ]
    ]
    [ paneHeader "State"
    , span
        [ classes
            [ btn
            , btnSmall
            ]
        ]
        [ strong_
            [ text "Contract expiration (slot):"
            ]
        , span
            [ class_ $ ClassName "max-contract-length"
            ]
            [ view (_marloweState <<< _Head <<< _contract <<< to contractMaxTime <<< to text) state
            ]
        , strong_
            [ text "Current Block:"
            ]
        , span
            [ class_ $ ClassName "block-number"
            ]
            [ view (_marloweState <<< _Head <<< _slot <<< to show <<< to text) state
            ]
        ]
    ]
  where
  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) = let t = maxTime contract in if t == zero then "Closed" else show t

statePane :: forall p. FrontendState -> HTML p HAction
statePane state =
  div
    [ class_ $ ClassName "col"
    ]
    [ stateTable state
    ]

stateTable :: forall p. FrontendState -> HTML p HAction
stateTable state =
  div_
    [ card_
        [ cardBody_
            [ h3_
                [ text "Accounts"
                ]
            , div
                [ classes [ ClassName "state-row", ClassName "full-width-card-5" ] ]
                [ if (Map.size accounts == 0) then
                    text "There are no accounts in the state"
                  else
                    renderAccounts accounts
                ]
            , h3_
                [ text "Choices"
                ]
            , div
                [ classes [ ClassName "state-row", ClassName "full-width-card" ] ]
                [ if (Map.size choices == 0) then
                    text "No choices have been recorded"
                  else
                    renderChoices choices
                ]
            , h3_
                [ text "Payments"
                ]
            , div
                [ classes [ ClassName "state-row", ClassName "full-width-card-4" ] ]
                [ if (Array.length payments == 0) then
                    text "No payments have been recorded"
                  else
                    renderPayments payments
                ]
            , h3_
                [ text "Let bindings"
                ]
            , div
                [ classes [ ClassName "state-last-row", ClassName "full-width-card" ] ]
                [ if (Map.size bindings == 0) then
                    text "No values have been bound"
                  else
                    renderBindings bindings
                ]
            ]
        ]
    ]
  where
  accounts = state ^. _marloweState <<< _Head <<< _state <<< _accounts

  choices = state ^. _marloweState <<< _Head <<< _state <<< _choices

  payments = state ^. _marloweState <<< _Head <<< _payments

  bindings = state ^. _marloweState <<< _Head <<< _state <<< _boundValues

renderAccounts :: forall p. Map (Tuple AccountId Token) BigInteger -> HTML p HAction
renderAccounts accounts =
  table_
    [ colgroup []
        [ col []
        , col []
        , col []
        ]
    , thead_
        [ tr []
            [ th_
                [ text "Account id"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Participant"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Currency symbol"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Token name"
                ]
            , th_
                [ text "Money"
                ]
            ]
        ]
    , tbody_ (map renderAccount accountList)
    ]
  where
  accountList = Map.toUnfoldable accounts :: Array (Tuple (Tuple AccountId Token) BigInteger)

renderAccount :: forall p. Tuple (Tuple AccountId Token) BigInteger -> HTML p HAction
renderAccount (Tuple (Tuple (AccountId accountNumber accountOwner) (Token currSym tokName)) value) =
  tr []
    [ td_
        [ text (show accountNumber)
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show accountOwner)
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show currSym)
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show tokName)
        ]
    , td_
        [ text (show value)
        ]
    ]

renderChoices :: forall p. Map ChoiceId ChosenNum -> HTML p HAction
renderChoices choices =
  table_
    [ colgroup []
        [ col []
        , col []
        , col []
        ]
    , thead_
        [ tr []
            [ th_
                [ text "Choice id"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Participant"
                ]
            , th_
                [ text "Chosen value"
                ]
            ]
        ]
    , tbody_ (map renderChoice choiceList)
    ]
  where
  choiceList = Map.toUnfoldable choices :: Array (Tuple ChoiceId ChosenNum)

renderChoice :: forall p. Tuple ChoiceId ChosenNum -> HTML p HAction
renderChoice (Tuple (ChoiceId choiceName choiceOwner) value) =
  tr []
    [ td_
        [ text (show choiceName)
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show choiceOwner)
        ]
    , td_
        [ text (show value)
        ]
    ]

renderPayments :: forall p. Array Payment -> HTML p HAction
renderPayments payments =
  table_
    [ colgroup []
        [ col []
        , col []
        , col []
        ]
    , thead_
        [ tr []
            [ th_
                [ text "Party"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Currency symbol"
                ]
            , th
                [ class_ $ ClassName "middle-column"
                ]
                [ text "Token name"
                ]
            , th
                [ class_ $ ClassName "left-border-column"
                ]
                [ text "Money"
                ]
            ]
        ]
    , tbody_ (flattenPayments payments)
    ]

flattenPayments :: forall p. Array Payment -> Array (HTML p HAction)
flattenPayments payments =
  concatMap
    ( \(Payment party (Assets mon)) ->
        concatMap
          ( \(Tuple curr toks) ->
              map
                ( \(Tuple tok val) ->
                    renderPayment party curr tok val
                )
                $ Map.toUnfoldable toks
          )
          $ Map.toUnfoldable mon
    )
    payments

renderPayment :: forall p. Party -> CurrencySymbol -> TokenName -> BigInteger -> HTML p HAction
renderPayment party currSym tokName money =
  tr []
    [ td_
        [ text party
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show currSym)
        ]
    , td
        [ class_ $ ClassName "middle-column"
        ]
        [ text (show tokName)
        ]
    , td
        [ class_ $ ClassName "left-border-column"
        ]
        [ text (show money)
        ]
    ]

renderBindings :: forall p. Map ValueId BigInteger -> HTML p HAction
renderBindings bindings =
  table_
    [ colgroup []
        [ col []
        , col []
        , col []
        ]
    , thead_
        [ tr []
            [ th_
                [ text "Identifier"
                ]
            , th
                [ class_ $ ClassName "left-border-column"
                ]
                [ text "Value"
                ]
            ]
        ]
    , tbody_ (map renderBinding bindingList)
    ]
  where
  bindingList = Map.toUnfoldable bindings :: Array (Tuple ValueId BigInteger)

renderBinding :: forall p. Tuple ValueId BigInteger -> HTML p HAction
renderBinding (Tuple (ValueId valueId) value) =
  tr []
    [ td_
        [ text (show valueId)
        ]
    , td
        [ class_ $ ClassName "left-border-column"
        ]
        [ text (show value)
        ]
    ]

analysisPane :: forall p. FrontendState -> HTML p HAction
analysisPane state =
  div [ class_ $ ClassName "full-width-card" ]
    [ paneHeader "Static analysis"
    , card_
        [ cardBody_
            [ analysisResultPane state
            , button
                [ classes
                    [ btn
                    , btnPrimary
                    , ClassName "transaction-btn"
                    ]
                , onClick $ const $ Just $ AnalyseContract
                , enabled $ state ^. _analysisState <<< to (not isLoading)
                ]
                [ loading
                , text btnText
                ]
            ]
        ]
    ]
  where
  btnText = case state ^. _analysisState of
    Loading -> "  Analysing..."
    _ -> "Analyse Contract"

  loading = case state ^. _analysisState of
    Loading ->
      span
        [ classes
            [ ClassName "spinner-border"
            , ClassName "spinner-border-sm"
            ]
        , prop (PropName "role") "status"
        , prop (PropName "aria-hidden") "true"
        ]
        []
    _ -> empty

analysisResultPane :: forall p. FrontendState -> HTML p HAction
analysisResultPane state =
  let
    result = state ^. _analysisState
  in
    case result of
      NotAsked ->
        div [ classes [ ClassName "padded-explanation" ] ]
          [ text "Press the button below to analyse the contract for runtime warnings." ]
      Success (R.Valid) ->
        div [ classes [ ClassName "padded-explanation" ] ]
          [ h3_ [ text "Analysis Result: Pass" ]
          , text "Static analysis could not find any execution that results in any warning."
          ]
      Success (R.CounterExample { initialSlot, transactionList, transactionWarning }) ->
        div [ classes [ ClassName "padded-explanation" ] ]
          [ h3_ [ text "Analysis Result: Fail" ]
          , text "Static analysis found the following counterexample:"
          , ul_
              [ li_
                  [ spanText "Initial slot: "
                  , b_ [ spanText (show initialSlot) ]
                  ]
              , li_
                  [ spanText "Offending transaction list: "
                  , displayTransactionList transactionList
                  ]
              , li_
                  [ spanText "Warnings issued: "
                  , displayWarningList transactionWarning
                  ]
              ]
          ]
      Success (R.Error str) ->
        div [ classes [ ClassName "padded-explanation" ] ]
          [ h3_ [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul_
              [ li_
                  [ b_ [ spanText str ]
                  ]
              ]
          ]
      Failure failure ->
        div [ classes [ ClassName "padded-explanation" ] ]
          [ h3_ [ text "Error during analysis" ]
          , text "Analysis failed for the following reason:"
          , ul_
              [ li_
                  [ b_ [ spanText failure ]
                  ]
              ]
          ]
      _ -> empty

displayTransactionList :: forall p. String -> HTML p HAction
displayTransactionList transactionList = case runParser transactionList transactionInputList of
  Right pTL ->
    ol_
      ( do
          ( TransactionInput
              { interval: SlotInterval (Slot from) (Slot to)
            , inputs: inputList
            }
          ) <-
            ((toUnfoldable pTL) :: Array TransactionInput)
          pure
            ( li_
                [ span_
                    [ b_ [ text "Transaction" ]
                    , text " with slot interval "
                    , b_ [ text $ (show from <> " to " <> show to) ]
                    , if null inputList then
                        text " and no inputs (empty transaction)."
                      else
                        text " and inputs:"
                    ]
                , if null inputList then
                    empty
                  else
                    displayInputList inputList
                ]
            )
      )
  Left _ -> code_ [ text transactionList ]

displayInputList :: forall p. List Input -> HTML p HAction
displayInputList inputList =
  ol_
    ( do
        input <- (toUnfoldable inputList)
        pure (li_ (displayInput input))
    )

displayInput :: forall p. Input -> Array (HTML p HAction)
displayInput (IDeposit (AccountId accNum owner) party tok money) =
  [ b_ [ text "IDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " deposits "
  , b_ [ text $ show money ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " into account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text "."
  ]

displayInput (IChoice (ChoiceId choiceId party) chosenNum) =
  [ b_ [ text "IChoice" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " chooses number "
  , b_ [ text $ show chosenNum ]
  , text " for choice "
  , b_ [ text $ show choiceId ]
  , text "."
  ]

displayInput (INotify) =
  [ b_ [ text "INotify" ]
  , text " - The contract is notified that an observation became "
  , b_ [ text "True" ]
  ]

displayWarningList :: forall p. String -> HTML p HAction
displayWarningList transactionWarnings = case runParser transactionWarnings transactionWarningList of
  Right pWL ->
    ol_
      ( do
          warning <- ((toUnfoldable pWL) :: Array TransactionWarning)
          pure (li_ (displayWarning warning))
      )
  Left _ -> code_ [ text transactionWarnings ]

displayWarnings :: forall p. Array TransactionWarning -> HTML p HAction
displayWarnings [] = text mempty

displayWarnings warnings =
  div
    [ classes
        [ ClassName "invalid-transaction"
        , ClassName "input-composer"
        ]
    ]
    [ h2 [] [ text "Warnings" ]
    , ol
        []
        $ foldMap (\warning -> [ li_ (displayWarning warning) ]) warnings
    ]

displayWarning :: forall p. TransactionWarning -> Array (HTML p HAction)
displayWarning (TransactionNonPositiveDeposit party (AccountId accNum owner) tok amount) =
  [ b_ [ text "TransactionNonPositiveDeposit" ]
  , text " - Party "
  , b_ [ text $ show party ]
  , text " is asked to deposit "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " into account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text "."
  ]

displayWarning (TransactionNonPositivePay (AccountId accNum owner) payee tok amount) =
  [ b_ [ text "TransactionNonPositivePay" ]
  , text " - The contract is suppoused to make a payment of "
  , b_ [ text $ show amount ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " from account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text " to "
  , b_
      [ text case payee of
          (Account (AccountId accNum2 owner2)) -> ("account " <> (show accNum2) <> " of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text "."
  ]

displayWarning (TransactionPartialPay (AccountId accNum owner) payee tok amount expected) =
  [ b_ [ text "TransactionPartialPay" ]
  , text " - The contract is suppoused to make a payment of "
  , b_ [ text $ show expected ]
  , text " units of "
  , b_ [ text $ show tok ]
  , text " from account "
  , b_ [ text ((show accNum) <> " of " <> (show owner)) ]
  , text " to "
  , b_
      [ text case payee of
          (Account (AccountId accNum2 owner2)) -> ("account " <> (show accNum2) <> " of " <> (show owner2))
          (Party dest) -> ("party " <> (show dest))
      ]
  , text " but there is only "
  , b_ [ text $ show amount ]
  , text "."
  ]

displayWarning (TransactionShadowing valId oldVal newVal) =
  [ b_ [ text "TransactionShadowing" ]
  , text " - The contract defined the value with id "
  , b_ [ text (show valId) ]
  , text " before, it was assigned the value "
  , b_ [ text (show oldVal) ]
  , text " and now it is being assigned the value "
  , b_ [ text (show newVal) ]
  , text "."
  ]
