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
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Newtype (unwrap, wrap)
import Data.String (trim)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen (RefLabel(..))
import Halogen.Classes (aHorizontal, bold, btn, flex, flexCol, flexGrow, flexShrink0, fontBold, fullHeight, fullWidth, grid, gridColsDescriptionLocation, group, justifyBetween, justifyCenter, justifyEnd, maxH70p, minH0, noMargins, overflowHidden, overflowScroll, paddingX, plusBtn, smallBtn, smallSpaceBottom, spaceBottom, spaceLeft, spaceRight, spanText, spanTextBreakWord, textSecondaryColor, textXs, uppercase, w30p)
import Halogen.Css (classNames)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, aside, b_, button, div, div_, em_, h6, h6_, input, li, li_, p, p_, section, slot, span, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), class_, classes, disabled, placeholder, type_, value)
import Halogen.Monaco (Settings, monacoComponent)
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe.Extended.Metadata (MetaData)
import Marlowe.Monaco (daylightTheme, languageExtensionPoint)
import Marlowe.Monaco as MM
import Marlowe.Semantics (AccountId, Assets(..), Bound(..), ChoiceId(..), Input(..), Party(..), Payment(..), PubKey, Slot, SlotInterval(..), Token(..), TransactionInput(..), inBounds, timeouts)
import Marlowe.Template (IntegerTemplateType(..))
import Monaco (Editor)
import Monaco as Monaco
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import SimulationPage.BottomPanel (panelContents)
import SimulationPage.Lenses (_bottomPanelState)
import SimulationPage.Types (Action(..), BottomPanelView(..), State)
import Simulator.Lenses (_SimulationRunning, _currentContract, _currentMarloweState, _executionState, _log, _marloweState, _possibleActions, _slot, _transactionError, _transactionWarnings)
import Simulator.State (hasHistory, inFuture)
import Simulator.Types (ActionInput(..), ActionInputId, ExecutionState(..), InitialConditionsRecord, LogEntry(..), otherActionsParty)
import Text.Markdown.TrimmedInline (markdownToHTML)

render ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  ComponentHTML Action ChildSlots m
render metadata state =
  div [ classes [ fullHeight, paddingX, flex ] ]
    [ div [ classes [ flex, flexCol, fullHeight, flexGrow ] ]
        [ section [ classes [ minH0, flexGrow, overflowHidden ] ]
            [ marloweEditor state ]
        , section [ classes [ maxH70p ] ]
            [ renderSubmodule
                _bottomPanelState
                BottomPanelAction
                (BottomPanel.render panelTitles wrapBottomPanelContents)
                state
            ]
        ]
    , aside [ classes [ flexShrink0, spaceLeft, overflowScroll, w30p ] ]
        (sidebar metadata state)
    ]
  where
  panelTitles =
    [ { title: "Current State", view: CurrentStateView, classes: [] }
    ]

  currentStateClasses = if hasRuntimeWarnings || hasRuntimeError then [ ClassName "error-tab" ] else []

  -- QUESTION: what are runtimeWarnings and runtimeError? how can I reach that state?
  hasRuntimeWarnings = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionWarnings <<< to Array.null <<< only false) state

  hasRuntimeError = has (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _transactionError <<< to isJust <<< only true) state

  wrapBottomPanelContents panelView = BottomPanelTypes.PanelAction <$> panelContents metadata state panelView

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
    , classNames [ "btn" ]
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
  MetaData ->
  State ->
  Array (HTML p Action)
sidebar metadata state = case view (_marloweState <<< _Head <<< _executionState) state of
  SimulationNotStarted notStartedRecord -> [ startSimulationWidget metadata notStartedRecord ]
  SimulationRunning _ ->
    [ div [ class_ smallSpaceBottom ] [ simulationStateWidget state ]
    , div [ class_ spaceBottom ] [ actionWidget metadata state ]
    , logWidget metadata state
    ]

------------------------------------------------------------
startSimulationWidget :: forall p. MetaData -> InitialConditionsRecord -> HTML p Action
startSimulationWidget metadata { initialSlot, templateContent } =
  cardWidget "Simulation has not started yet"
    $ div_
        [ div [ classes [ ClassName "slot-input", ClassName "initial-slot-input" ] ]
            [ spanText "Initial slot:"
            , marloweActionInput (SetInitialSlot <<< wrap) initialSlot
            ]
        , div_
            [ ul [ class_ (ClassName "templates") ]
                ( integerTemplateParameters metadata.slotParameterDescriptions SetIntegerTemplateParam SlotContent "Timeout template parameters" "Slot for" (unwrap templateContent).slotContent
                    <> integerTemplateParameters metadata.valueParameterDescriptions SetIntegerTemplateParam ValueContent "Value template parameters" "Constant for" (unwrap templateContent).valueContent
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

integerTemplateParameters :: forall action p. Map String String -> (IntegerTemplateType -> String -> BigInteger -> action) -> IntegerTemplateType -> String -> String -> Map String BigInteger -> Array (HTML p action)
integerTemplateParameters explanations actionGen typeName title prefix content =
  [ li_
      if Map.isEmpty content then
        []
      else
        ([ h6_ [ em_ [ text title ] ] ])
          <> ( map
                ( \(key /\ value) ->
                    ( ( div [ class_ (ClassName "template-fields") ]
                          ( [ div_
                                [ text (prefix <> " ")
                                , strong_ [ text key ]
                                , text ":"
                                ]
                            , marloweActionInput (actionGen typeName key) value
                            ]
                              <> [ div [ classes [ ClassName "action-group-explanation" ] ]
                                    $ maybe [] (\explanation -> [ text "“" ] <> markdownToHTML explanation <> [ text "„" ])
                                    $ Map.lookup key explanations
                                ]
                          )
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
  MetaData ->
  State ->
  HTML p Action
actionWidget metadata state =
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
  actionsForParties m = map (\(Tuple k v) -> participant metadata state k (vs v)) (sortParties (kvs m))

participant ::
  forall p.
  MetaData ->
  State ->
  Party ->
  Array ActionInput ->
  HTML p Action
participant metadata state party actionInputs =
  li [ classes [ noMargins ] ]
    ( [ title ]
        <> (map (inputItem metadata state partyName) actionInputs)
    )
  where
  title =
    div [ classes [ ClassName "action-group" ] ]
      if party == otherActionsParty then
        -- QUESTION: if we only have "move to slot", could we rename this to "Slot Actions"?
        [ div [ classes [ ClassName "action-group-title" ] ] [ h6_ [ em_ [ text "Other Actions" ] ] ] ]
      else
        [ div [ classes [ ClassName "action-group-title" ] ] [ h6_ [ em_ [ text "Participant ", strong_ [ text partyName ] ] ] ] ]
          <> [ div [ classes [ ClassName "action-group-explanation" ] ]
                ( case party of
                    Role roleName -> maybe [] (\explanation -> [ text "“" ] <> markdownToHTML explanation <> [ text "„" ]) $ Map.lookup roleName metadata.roleDescriptions
                    _ -> []
                )
            ]

  partyName = case party of
    (PK name) -> name
    (Role name) -> name

inputItem ::
  forall p.
  MetaData ->
  State ->
  PubKey ->
  ActionInput ->
  HTML p Action
inputItem metadata _ person (DepositInput accountId party token value) =
  div [ classes [ ClassName "action", aHorizontal ] ]
    [ renderDeposit metadata accountId party token value
    , div [ class_ (ClassName "align-top") ]
        [ button
            [ classes [ plusBtn, smallBtn, btn ]
            , onClick $ const $ Just
                $ AddInput (IDeposit accountId party token value) []
            ]
            [ text "+" ]
        ]
    ]

inputItem metadata _ person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  div
    [ classes [ ClassName "action", aHorizontal, ClassName "flex-nowrap" ] ]
    ( [ div [ classes [ ClassName "action-label" ] ]
          ( [ div [ class_ (ClassName "choice-input") ]
                [ span [ class_ (ClassName "break-word-span") ] [ text "Choice ", b_ [ text (show choiceName <> ": ") ] ]
                , marloweActionInput (SetChoice choiceId) chosenNum
                ]
            , div [ class_ (ClassName "choice-error") ] error
            ]
              <> ( maybe []
                    ( \explanation ->
                        [ div [ class_ (ClassName "action-explanation") ]
                            ([ text "“" ] <> markdownToHTML explanation <> [ text "„" ])
                        ]
                    )
                    (Map.lookup choiceName metadata.choiceInfo >>= mExtractDescription)
                )
          )
      ]
        <> addButton
    )
  where
  mExtractDescription { choiceDescription }
    | trim choiceDescription /= "" = Just choiceDescription

  mExtractDescription _ = Nothing

  addButton =
    if inBounds chosenNum bounds then
      [ button
          [ classes [ btn, plusBtn, smallBtn, ClassName "align-top", ClassName "flex-noshrink" ]
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

inputItem _ _ person NotifyInput =
  li
    [ classes [ ClassName "action", ClassName "choice-a", aHorizontal ] ]
    [ p_ [ text "Notify Contract" ]
    , button
        [ classes [ btn, plusBtn, smallBtn, ClassName "align-top" ]
        , onClick $ const $ Just
            $ AddInput INotify []
        ]
        [ text "+" ]
    ]

inputItem _ state person (MoveToSlot slot) =
  div
    [ classes [ aHorizontal, ClassName "flex-nowrap" ] ]
    ( [ div [ classes [ ClassName "action" ] ]
          [ p [ class_ (ClassName "slot-input") ]
              [ spanTextBreakWord "Move to slot "
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
          [ classes [ plusBtn, smallBtn, ClassName "align-top", ClassName "flex-noshrink", btn ]
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

renderDeposit :: forall p. MetaData -> AccountId -> Party -> Token -> BigInteger -> HTML p Action
renderDeposit metadata accountOwner party tok money =
  span [ classes [ ClassName "break-word-span" ] ]
    [ text "Deposit "
    , strong_ [ text (showPrettyMoney money) ]
    , text " units of "
    , strong_ [ renderPrettyToken tok ]
    , text " into account of "
    , strong_ [ renderPrettyParty metadata accountOwner ]
    , text " as "
    , strong_ [ renderPrettyParty metadata party ]
    ]

------------------------------------------------------------
logWidget ::
  forall p.
  MetaData ->
  State ->
  HTML p Action
logWidget metadata state =
  cardWidget "Transaction log"
    $ div [ classes [ grid, gridColsDescriptionLocation, fullWidth ] ]
        ( [ div [ class_ fontBold ] [ text "Action" ]
          , div [ class_ fontBold ] [ text "Slot" ]
          ]
            <> inputLines
        )
  where
  inputLines = state ^. (_marloweState <<< _Head <<< _executionState <<< _SimulationRunning <<< _log <<< to (concatMap (logToLines metadata) <<< reverse))

logToLines :: forall p a. MetaData -> LogEntry -> Array (HTML p a)
logToLines metadata (StartEvent slot) =
  [ span_ [ text "Contract started" ]
  , span [ class_ justifyEnd ] [ text $ show slot ]
  ]

logToLines metadata (InputEvent (TransactionInput { interval, inputs })) = inputToLine metadata interval =<< Array.fromFoldable inputs

logToLines metadata (OutputEvent interval payment) = paymentToLines metadata interval payment

logToLines metadata (CloseEvent (SlotInterval start end)) =
  [ span_ [ text $ "Contract ended" ]
  , span [ class_ justifyEnd ] [ text $ showSlotRange start end ]
  ]

inputToLine :: forall p a. MetaData -> SlotInterval -> Input -> Array (HTML p a)
inputToLine metadata (SlotInterval start end) (IDeposit accountOwner party token money) =
  [ span_
      [ text "Deposit "
      , strong_ [ text (showPrettyMoney money) ]
      , text " units of "
      , strong_ [ renderPrettyToken token ]
      , text " into account of "
      , strong_ [ renderPrettyParty metadata accountOwner ]
      , text " as "
      , strong_ [ renderPrettyParty metadata party ]
      ]
  , span [ class_ justifyEnd ] [ text $ showSlotRange start end ]
  ]

inputToLine metadata (SlotInterval start end) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
  [ span_
      [ text "Participant "
      , strong_ [ renderPrettyParty metadata choiceOwner ]
      , text " chooses the value "
      , strong_ [ text (showPrettyMoney chosenNum) ]
      , text " for choice with id "
      , strong_ [ text (show choiceName) ]
      ]
  , span [ class_ justifyEnd ] [ text $ showSlotRange start end ]
  ]

inputToLine _ (SlotInterval start end) INotify =
  [ text "Notify"
  , span [ class_ justifyEnd ] [ text $ showSlotRange start end ]
  ]

paymentToLines :: forall p a. MetaData -> SlotInterval -> Payment -> Array (HTML p a)
paymentToLines metadata slotInterval (Payment party money) = join $ unfoldAssets money (paymentToLine metadata slotInterval party)

paymentToLine :: forall p a. MetaData -> SlotInterval -> Party -> Token -> BigInteger -> Array (HTML p a)
paymentToLine metadata (SlotInterval start end) party token money =
  [ span_
      [ text "The contract pays "
      , strong_ [ text (showPrettyMoney money) ]
      , text " units of "
      , strong_ [ renderPrettyToken token ]
      , text " to participant "
      , strong_ [ renderPrettyParty metadata party ]
      ]
  , span [ class_ justifyEnd ] [ text $ showSlotRange start end ]
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
