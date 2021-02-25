module SimulationPage.View where

import Prelude hiding (div)
import BottomPanel.Types as BottomPanelTypes
import BottomPanel.View as BottomPanel
import Data.Array (concatMap, intercalate, reverse, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Lens (has, only, previewOn, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (unwrap, wrap)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen (RefLabel(..))
import Halogen.Classes (aHorizontal, bold, btn, codeEditor, expanded, flex, fullHeight, group, justifyBetween, justifyCenter, noMargins, plusBtn, sidebarComposer, smallBtn, smallSpaceBottom, spaceBottom, spaceRight, spanText, textSecondaryColor, textXs, uppercase)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, aside, b_, br_, button, div, div_, em_, h6, h6_, input, li, li_, p, p_, section, slot, span, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, disabled, placeholder, type_, value)
import Halogen.Monaco (Settings, monacoComponent)
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe.Extended (IntegerTemplateType(..))
import Marlowe.Monaco (daylightTheme, languageExtensionPoint)
import Marlowe.Monaco as MM
import Marlowe.Semantics (AccountId, Assets(..), Bound(..), ChoiceId(..), Input(..), Party(..), Payment(..), PubKey, Slot, SlotInterval(..), Token(..), TransactionInput(..), inBounds, timeouts)
import Monaco (Editor)
import Monaco as Monaco
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import SimulationPage.BottomPanel (panelContents)
import SimulationPage.Types (Action(..), ActionInput(..), ActionInputId, BottomPanelView(..), ExecutionState(..), InitialConditionsRecord, MarloweEvent(..), State, _SimulationRunning, _bottomPanelState, _currentContract, _currentMarloweState, _executionState, _log, _marloweState, _possibleActions, _showRightPanel, _slot, _transactionError, _transactionWarnings, otherActionsParty)
import Simulator (hasHistory, inFuture)

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ fullHeight, ClassName "simulation-panel" ] ]
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes [ codeEditor ] ]
            [ marloweEditor state ]
        , sidebar state
        ]
    , renderSubmodule _bottomPanelState BottomPanelAction (BottomPanel.render panelTitles wrapBottomPanelContents) state
    ]
  where
  panelTitles =
    [ { title: "Current State", view: CurrentStateView, classes: [] }
    ]

  currentStateClasses = if hasRuntimeWarnings || hasRuntimeError then [ ClassName "error-tab" ] else []

  -- QUESTION: what are runtimeWarnings and runtimeError? how can I reach that state?
  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  showRightPanel = state ^. _showRightPanel

  wrapBottomPanelContents panelView = BottomPanelTypes.PanelAction <$> panelContents state panelView

otherActions :: forall p. State -> HTML p Action
otherActions state =
  div [ classes [ group ] ]
    [ editSourceButton ]

{-
    FIXME: This code was disabled because we changed "source" to "workflow" and
           we move it to the MainFrame. This posses a challenge, were this subcomponent
           needs to see information from the parent state which is not available in the
           subcomponent state.
           There were four possible solutions to this problem:
             * the easy but error prone would be to duplicate state in the MainFrame and here
             * we could change the type of Simulation.State to be
                type State =
                  { ownState :: OwnState -- what we currently call State
                  , parentState :: ProjectedState -- what data from the parent we need in this view, namely workflow
                  }
                or
                type State =
                  { simulationState :: Simulation.OwnState
                  , workflow :: Maybe Workflow
                  }
               which is similar but more "direct", and use a custom lense to provide access to both
               parts of the state.
             * Add the notion of "input" to the subcomponents, similar to what Halogen components do
             * we can reduce functionality and just say "Edit source"
           We opted for the last one as it's the simplest and least conflicting. In January the frontend
           team should meet to discuss the alternatives.
    [ sendToBlocklyButton state
      ]
        <> ( if has (_source <<< only Haskell) state then
              [ haskellSourceButton state ]
            else
              []
          )
        <> ( if has (_source <<< only Javascript) state then
              [ javascriptSourceButton state ]
            else
              []
          )
        <> ( if has (_source <<< only Actus) state then
              [ actusSourceButton state ]
            else
              []
          )

sendToBlocklyButton :: forall p. State -> HTML p Action
sendToBlocklyButton state =
  button
    [ onClick $ const $ Just $ SetBlocklyCode
    , enabled isBlocklyEnabled
    , classes [ Classes.disabled (not isBlocklyEnabled) ]
    ]
    [ text "View in Blockly Editor" ]
  where
  isBlocklyEnabled = view (_marloweState <<< _Head <<< _editorErrors <<< to Array.null) state

haskellSourceButton :: forall p. State -> HTML p Action
haskellSourceButton state =
  button
    [ onClick $ const $ Just $ EditHaskell
    ]
    [ text "Edit Haskell Source" ]

javascriptSourceButton :: forall p. State -> HTML p Action
javascriptSourceButton state =
  button
    [ onClick $ const $ Just $ EditJavascript
    ]
    [ text "Edit Javascript Source" ]

actusSourceButton :: forall p. State -> HTML p Action
actusSourceButton state =
  button
    [ onClick $ const $ Just $ EditActus
    ]
    [ text "Edit Actus Source" ]
-}
editSourceButton :: forall p. HTML p Action
editSourceButton =
  button
    [ onClick $ const $ Just $ EditSource
    ]
    [ text "Edit source" ]

marloweEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
marloweEditor state = slot _simulatorEditorSlot unit component unit (const Nothing)
  where
  setup editor = do
    model <- liftEffect $ Monaco.getModel editor
    liftEffect do
      -- Since the Simulation Tab is viewed before the Haskell tab we need to set the correct editor theme when things have been loaded
      monaco <- Monaco.getMonaco
      Monaco.setTheme monaco MM.daylightTheme.name
      Monaco.setReadOnly editor true

  component = monacoComponent $ settings setup

refLabel :: RefLabel
refLabel = RefLabel "simulatorEditor"

settings :: forall m. (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Just daylightTheme
  , monarchTokensProvider: Nothing
  , tokensProvider: Nothing
  , hoverProvider: Nothing
  , completionItemProvider: Nothing
  , codeActionProvider: Nothing
  , documentFormattingEditProvider: Nothing
  , refLabel
  , owner: "marloweEditor"
  , setup
  }

------------------------------------------------------------
sidebar ::
  forall p.
  State ->
  HTML p Action
sidebar state =
  let
    showRightPanel = state ^. _showRightPanel

    contents = case view (_marloweState <<< _Head <<< _executionState) state of
      SimulationNotStarted notStartedRecord -> [ startSimulationWidget notStartedRecord ]
      SimulationRunning _ ->
        [ div [ class_ smallSpaceBottom ] [ simulationStateWidget state ]
        , div [ class_ spaceBottom ] [ actionWidget state ]
        , logWidget state
        ]
  in
    aside [ classes [ sidebarComposer, expanded showRightPanel ] ]
      {- FIXME the drawer icon to show/hide the right panel is currently not shown and is not present in the
                 designs. Check if we need to remove that functionality and if so, remove the action and state
                 that goes with it.
       div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel), ClassName "drawer-icon-container" ] ]
          [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (not showRightPanel) ]
              [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
          ]
        -}
      contents

{-
        FIXME The new designs of the simulator does not have contextual help, and there is a lot
        of code related to this. Confirm if we really don't want this before deleting, or if it may
        come back later on.
      , article [ class_ (ClassName "documentation-panel") ]
          (toHTML (state ^. _helpContext))
      -}
------------------------------------------------------------
startSimulationWidget :: forall p. InitialConditionsRecord -> HTML p Action
startSimulationWidget { initialSlot, templateContent } =
  cardWidget "Simulation has not started yet"
    $ div [ classes [] ]
        [ div [ classes [ ClassName "slot-input", ClassName "initial-slot-input" ] ]
            [ spanText "Initial slot:"
            , marloweActionInput (SetInitialSlot <<< wrap) initialSlot
            ]
        , div [ classes [] ]
            [ ul [ class_ (ClassName "templates") ]
                ( integerTemplateParameters SetIntegerTemplateParam SlotContent "Timeout template parameters" "Slot for" (unwrap templateContent).slotContent
                    <> integerTemplateParameters SetIntegerTemplateParam ValueContent "Value template parameters" "Constant for" (unwrap templateContent).valueContent
                )
            ]
        , div [ classes [ ClassName "transaction-btns", flex, justifyCenter ] ]
            [ button
                [ classes [ btn, bold ]
                , onClick $ const $ Just StartSimulation
                ]
                [ text "Start simulation" ]
            ]
        ]

integerTemplateParameters :: forall action p. (IntegerTemplateType -> String -> BigInteger -> action) -> IntegerTemplateType -> String -> String -> Map String BigInteger -> Array (HTML p action)
integerTemplateParameters actionGen typeName title prefix content =
  [ li_
      if Map.isEmpty content then
        []
      else
        ([ h6_ [ em_ [ text title ] ] ])
          <> ( map
                ( \(key /\ value) ->
                    ( ( div [ class_ (ClassName "template-fields") ]
                          [ text (prefix <> " ")
                          , strong_ [ text key ]
                          , text ":"
                          , marloweActionInput (actionGen typeName key) value
                          ]
                      )
                    )
                )
                (Map.toUnfoldable content)
            )
  ]

------------------------------------------------------------
simulationStateWidget ::
  forall p.
  State ->
  HTML p Action
simulationStateWidget state =
  let
    currentSlot = state ^. (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< to show)

    expirationSlot = contractMaxTime (previewOn state _currentContract)

    contractMaxTime = case _ of
      Nothing -> "Closed"
      Just contract ->
        let
          t = (_.maxTime <<< unwrap <<< timeouts) contract
        in
          if t == zero then "Closed" else show t

    indicator name value =
      div_
        [ span
            [ class_ bold ]
            [ text $ name <> ": " ]
        , span_ [ text value ]
        ]
  in
    div
      [ classes [ flex, justifyBetween ] ]
      [ indicator "current slot" currentSlot
      , indicator "expiration slot" expirationSlot
      ]

------------------------------------------------------------
actionWidget ::
  forall p.
  State ->
  HTML p Action
actionWidget state =
  cardWidget "Actions"
    $ div [ classes [] ]
        [ ul [ class_ (ClassName "participants") ]
            if (Map.isEmpty possibleActions) then
              [ text "No valid inputs can be added to the transaction" ]
            else
              (actionsForParties possibleActions)
        , div [ classes [ ClassName "transaction-btns", flex, justifyCenter ] ]
            [ button
                [ classes [ btn, bold, spaceRight ]
                , disabled $ not $ hasHistory state
                , onClick $ const $ Just Undo
                ]
                [ text "Undo" ]
            , button
                [ classes [ btn, bold ]
                , onClick $ const $ Just ResetSimulator
                ]
                [ text "Reset" ]
            ]
        ]
  where
  possibleActions = view (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _possibleActions <<< _Newtype) state

  kvs :: forall k v. Map k v -> Array (Tuple k v)
  kvs = Map.toUnfoldable

  vs :: forall k v. Map k v -> Array v
  vs m = map snd (kvs m)

  lastKey :: Maybe Party
  lastKey = map (\x -> x.key) (Map.findMax possibleActions)

  sortParties :: forall v. Array (Tuple Party v) -> Array (Tuple Party v)
  sortParties = sortWith (\(Tuple party _) -> party == otherActionsParty)

  actionsForParties :: Map Party (Map ActionInputId ActionInput) -> Array (HTML p Action)
  actionsForParties m = map (\(Tuple k v) -> participant state k (vs v)) (sortParties (kvs m))

participant ::
  forall p.
  State ->
  Party ->
  Array ActionInput ->
  HTML p Action
participant state party actionInputs =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    ( [ h6_ [ em_ title ] ]
        <> (map (inputItem state partyName) actionInputs)
    )
  where
  title =
    if party == otherActionsParty then
      -- QUESTION: if we only have "move to slot", could we rename this to "Slot Actions"?
      [ text "Other Actions" ]
    else
      [ text "Participant ", strong_ [ text partyName ] ]

  partyName = case party of
    (PK name) -> name
    (Role name) -> name

inputItem ::
  forall p.
  State ->
  PubKey ->
  ActionInput ->
  HTML p Action
inputItem _ person (DepositInput accountId party token value) =
  div [ classes [ aHorizontal ] ]
    [ p_ (renderDeposit accountId party token value)
    , div [ class_ (ClassName "align-top") ]
        [ button
            [ classes [ plusBtn, smallBtn ]
            , onClick $ const $ Just
                $ AddInput (IDeposit accountId party token value) []
            ]
            [ text "+" ]
        ]
    ]

inputItem _ person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "choice-input") ]
              [ spanText "Choice "
              , b_ [ spanText (show choiceName <> ":") ]
              , br_
              , spanText "Choose value "
              , marloweActionInput (SetChoice choiceId) chosenNum
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if inBounds chosenNum bounds then
      [ button
          [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
          , onClick $ const $ Just
              $ AddInput (IChoice (ChoiceId choiceName choiceOwner) chosenNum) bounds
          ]
          [ text "+" ]
      ]
    else
      []

  error = if inBounds chosenNum bounds then [] else [ text boundsError ]

  boundsError =
    if Array.null bounds then
      "A choice must have set bounds, please fix the contract"
    else
      "Choice must be between " <> intercalate " or " (map boundError bounds)

  boundError (Bound from to) = show from <> " and " <> show to

inputItem _ person NotifyInput =
  li
    [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_ [ text "Notify Contract" ]
    , button
        [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
        , onClick $ const $ Just
            $ AddInput INotify []
        ]
        [ text "+" ]
    ]

inputItem state person (MoveToSlot slot) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "slot-input") ]
              [ spanText "Move to slot "
              , marloweActionInput (SetSlot <<< wrap) slot
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if inFuture state slot then
      [ button
          [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
          , onClick $ const $ Just $ MoveSlot slot
          ]
          [ text "+" ]
      ]
    else
      []

  error = if inFuture state slot then [] else [ text boundsError ]

  boundsError = "The slot must be more than the current slot " <> (state ^. (_currentMarloweState <<< _executionState <<< _SimulationRunning <<< _slot <<< to show))

marloweActionInput :: forall p a action. Show a => (BigInteger -> action) -> a -> HTML p action
marloweActionInput f current =
  input
    [ type_ InputNumber
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

renderDeposit :: forall p. AccountId -> Party -> Token -> BigInteger -> Array (HTML p Action)
renderDeposit accountOwner party tok money =
  [ spanText "Deposit "
  , b_ [ spanText (showPrettyMoney money) ]
  , spanText " units of "
  , b_ [ renderPrettyToken tok ]
  , spanText " into account of "
  , b_ [ renderPrettyParty accountOwner ]
  , spanText " as "
  , b_ [ renderPrettyParty party ]
  ]

------------------------------------------------------------
logWidget ::
  forall p.
  State ->
  HTML p Action
logWidget state =
  cardWidget "Transaction log"
    $ div []
        [ div
            [ classes [ ClassName "error-headers", ClassName "error-row" ] ]
            [ div [] [ text "Action" ]
            , div [] [ text "Slot" ]
            ]
        , ul [] (reverse inputLines)
        ]
  where
  inputLines = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _log <<< to (concatMap logToLines))

logToLines :: forall p a. MarloweEvent -> Array (HTML p a)
logToLines (InputEvent (TransactionInput { interval, inputs })) = Array.fromFoldable $ map (inputToLine interval) inputs

logToLines (OutputEvent interval payment) = paymentToLines interval payment

inputToLine :: forall p a. SlotInterval -> Input -> HTML p a
inputToLine (SlotInterval start end) (IDeposit accountOwner party token money) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Deposit "
        , strong_ [ text (showPrettyMoney money) ]
        , text " units of "
        , strong_ [ renderPrettyToken token ]
        , text " into account of "
        , strong_ [ renderPrettyParty accountOwner ]
        , text " as "
        , strong_ [ renderPrettyParty party ]
        ]
    , span_ [ text $ showSlotRange start end ]
    ]

inputToLine (SlotInterval start end) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "Participant "
        , strong_ [ renderPrettyParty choiceOwner ]
        , text " chooses the value "
        , strong_ [ text (showPrettyMoney chosenNum) ]
        , text " for choice with id "
        , strong_ [ text (show choiceName) ]
        ]
    , span_ [ text $ showSlotRange start end ]
    ]

inputToLine (SlotInterval start end) INotify =
  li [ classes [ ClassName "error-row" ] ]
    [ text "Notify"
    , span_ [ text $ showSlotRange start end ]
    ]

paymentToLines :: forall p a. SlotInterval -> Payment -> Array (HTML p a)
paymentToLines slotInterval (Payment party money) = unfoldAssets money (paymentToLine slotInterval party)

paymentToLine :: forall p a. SlotInterval -> Party -> Token -> BigInteger -> HTML p a
paymentToLine (SlotInterval start end) party token money =
  li [ classes [ ClassName "error-row" ] ]
    [ span_
        [ text "The contract pays "
        , strong_ [ text (showPrettyMoney money) ]
        , text " units of "
        , strong_ [ renderPrettyToken token ]
        , text " to participant "
        , strong_ [ renderPrettyParty party ]
        ]
    , span_ [ text $ showSlotRange start end ]
    ]

showSlotRange :: Slot -> Slot -> String
showSlotRange start end =
  if start == end then
    show start
  else
    (show start) <> " - " <> (show end)

unfoldAssets :: forall a. Assets -> (Token -> BigInteger -> a) -> Array a
unfoldAssets (Assets mon) f =
  concatMap
    ( \(Tuple currencySymbol tokenMap) ->
        ( map
            ( \(Tuple tokenName value) ->
                f (Token currencySymbol tokenName) value
            )
            (Map.toUnfoldable tokenMap)
        )
    )
    (Map.toUnfoldable mon)

------------------------------------------------------------
cardWidget :: forall p a. String -> HTML p a -> HTML p a
cardWidget name body =
  let
    title' = h6 [ classes [ noMargins, textSecondaryColor, bold, uppercase, textXs ] ] [ text name ]
  in
    div [ classes [ ClassName "simulation-card-widget" ] ]
      [ div [ class_ (ClassName "simulation-card-widget-header") ] [ title' ]
      , div [ class_ (ClassName "simulation-card-widget-body") ] [ body ]
      ]
