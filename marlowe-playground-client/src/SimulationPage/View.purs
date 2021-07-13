module SimulationPage.View where

import Prelude hiding (div)
import BottomPanel.Types as BottomPanelTypes
import BottomPanel.View as BottomPanel
import Data.Array (concatMap, intercalate, reverse, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Lens (has, only, previewOn, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Newtype (unwrap, wrap)
import Data.String (trim)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen.Classes (aHorizontal, bold, btn, flex, flexCol, flexGrow, flexShrink0, fontBold, fullHeight, fullWidth, grid, gridColsDescriptionLocation, group, justifyBetween, justifyCenter, justifyEnd, maxH70p, minH0, noMargins, overflowHidden, overflowScroll, paddingX, plusBtn, smallBtn, smallSpaceBottom, spaceBottom, spaceLeft, spaceRight, spanText, spanTextBreakWord, textSecondaryColor, textXs, uppercase, w30p)
import Halogen.Css (classNames)
import Halogen.CurrencyInput (currencyInput)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, PlainHTML, aside, b_, button, div, div_, em, em_, h4, h6, h6_, li, li_, p, p_, section, slot, span, span_, strong_, text, ul)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, disabled)
import Halogen.Monaco (monacoComponent)
import Hint.State (hint)
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe.Extended.Metadata (MetaData, NumberFormat(..), getChoiceFormat)
import Marlowe.Monaco as MM
import Marlowe.Semantics (AccountId, Assets(..), Bound(..), ChoiceId(..), Input(..), Party(..), Payee(..), Payment(..), PubKey, Slot, SlotInterval(..), Token(..), TransactionInput(..), inBounds, timeouts)
import Marlowe.Template (IntegerTemplateType(..))
import Material.Icons as Icon
import Monaco as Monaco
import Popper (Placement(..))
import Pretty (renderPrettyParty, renderPrettyPayee, renderPrettyToken, showPrettyChoice, showPrettyMoney)
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
marloweEditor state = slot _simulatorEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor = liftEffect $ Monaco.setReadOnly editor true

  component = monacoComponent $ MM.settings setup

------------------------------------------------------------
sidebar ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  Array (ComponentHTML Action ChildSlots m)
sidebar metadata state = case view (_marloweState <<< _Head <<< _executionState) state of
  SimulationNotStarted notStartedRecord -> [ startSimulationWidget metadata notStartedRecord ]
  SimulationRunning _ ->
    [ div [ class_ smallSpaceBottom ] [ simulationStateWidget state ]
    , div [ class_ spaceBottom ] [ actionWidget metadata state ]
    , logWidget metadata state
    ]

------------------------------------------------------------
type TemplateFormDisplayInfo a action
  = { lookupFormat :: String -> Maybe (String /\ Int) -- Gets the format for a given key
    , lookupDefinition :: String -> Maybe String -- Gets the definition for a given key
    , typeName :: IntegerTemplateType -- Identifier for the type of template we are displaying
    , title :: String -- Title of the section of the template type
    , prefix :: String -- Prefix for the explanation of the template
    }

startSimulationWidget ::
  forall m.
  MonadAff m =>
  MetaData ->
  InitialConditionsRecord ->
  ComponentHTML Action ChildSlots m
startSimulationWidget metadata { initialSlot, templateContent } =
  cardWidget "Simulation has not started yet"
    $ div_
        [ div [ classes [ ClassName "slot-input", ClassName "initial-slot-input" ] ]
            [ spanText "Initial slot:"
            , marloweActionInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (SetInitialSlot <<< wrap) (unwrap initialSlot)
            ]
        , div_
            [ ul [ class_ (ClassName "templates") ]
                ( integerTemplateParameters SetIntegerTemplateParam slotParameterDisplayInfo (unwrap templateContent).slotContent
                    <> integerTemplateParameters SetIntegerTemplateParam valueParameterDisplayInfo (unwrap templateContent).valueContent
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
  where
  slotParameterDisplayInfo =
    { lookupFormat: const Nothing
    , lookupDefinition: (flip Map.lookup) metadata.slotParameterDescriptions
    , typeName: SlotContent
    , title: "Timeout template parameters"
    , prefix: "Slot for"
    }

  valueParameterDisplayInfo =
    { lookupFormat: extractValueParameterNuberFormat
    , lookupDefinition: (flip lookupDescription) metadata.valueParameterInfo
    , typeName: ValueContent
    , title: "Value template parameters"
    , prefix: "Constant for"
    }

  extractValueParameterNuberFormat valueParameter = case Map.lookup valueParameter metadata.valueParameterInfo of
    Just { valueParameterFormat: DecimalFormat numDecimals currencyLabel } -> Just (currencyLabel /\ numDecimals)
    _ -> Nothing

  lookupDescription k m =
    ( case Map.lookup k m of
        Just { valueParameterDescription: description }
          | trim description /= "" -> Just description
        _ -> Nothing
    )

integerTemplateParameters ::
  forall a action m.
  MonadAff m =>
  (IntegerTemplateType -> String -> BigInteger -> action) ->
  TemplateFormDisplayInfo a action ->
  Map String BigInteger ->
  Array (ComponentHTML action ChildSlots m)
integerTemplateParameters actionGen { lookupFormat, lookupDefinition, typeName, title, prefix } content =
  let
    parameterHint key =
      maybe []
        ( \explanation ->
            [ hint
                [ "leading-none" ]
                ("template-parameter-" <> key)
                Auto
                (markdownHintWithTitle key explanation)
            ]
        )
        $ lookupDefinition key
  in
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
                              ]
                                <> parameterHint key
                                <> [ case lookupFormat key of
                                      Just (currencyLabel /\ numDecimals) -> marloweCurrencyInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (actionGen typeName key) currencyLabel numDecimals value
                                      Nothing -> marloweActionInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (actionGen typeName key) value
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
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  ComponentHTML Action ChildSlots m
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

  actionsForParties :: Map Party (Map ActionInputId ActionInput) -> Array (ComponentHTML Action ChildSlots m)
  actionsForParties m = map (\(Tuple k v) -> participant metadata state k (vs v)) (sortParties (kvs m))

participant ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  Party ->
  Array ActionInput ->
  ComponentHTML Action ChildSlots m
participant metadata state party actionInputs =
  li [ classes [ noMargins ] ]
    ( [ title ]
        <> (map (inputItem metadata state partyName) actionInputs)
    )
  where
  emptyDiv = div_ []

  partyHint = case party of
    Role roleName ->
      maybe emptyDiv
        ( \explanation ->
            hint
              [ "relative", "-top-1" ]
              ("participant-hint-" <> roleName)
              Auto
              (markdownHintWithTitle roleName explanation)
        )
        $ Map.lookup roleName metadata.roleDescriptions
    _ -> emptyDiv

  title =
    div [ classes [ ClassName "action-group" ] ]
      if party == otherActionsParty then
        -- QUESTION: if we only have "move to slot", could we rename this to "Slot Actions"?
        [ h6_ [ em_ [ text "Other Actions" ] ] ]
      else
        [ h6_
            [ em [ classNames [ "mr-1" ] ]
                [ text "Participant "
                , strong_ [ text partyName ]
                ]
            , partyHint
            ]
        ]

  partyName = case party of
    (PK name) -> name
    (Role name) -> name

inputItem ::
  forall m.
  MonadAff m =>
  MetaData ->
  State ->
  PubKey ->
  ActionInput ->
  ComponentHTML Action ChildSlots m
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
  let
    choiceHint =
      maybe (div_ [])
        ( \explanation ->
            hint
              [ "relative", "-top-1" ]
              ("choice-hint-" <> choiceName)
              Auto
              (markdownHintWithTitle choiceName explanation)
        )
        (mChoiceInfo >>= mExtractDescription)
  in
    div
      [ classes [ ClassName "action", aHorizontal, ClassName "flex-nowrap" ] ]
      ( [ div [ classes [ ClassName "action-label" ] ]
            [ div [ class_ (ClassName "choice-input") ]
                [ span [ class_ (ClassName "break-word-span") ]
                    [ text "Choice "
                    , b_ [ text (show choiceName <> ": ") ]
                    , choiceHint
                    ]
                , case mChoiceInfo of
                    Just { choiceFormat: DecimalFormat numDecimals currencyLabel } -> marloweCurrencyInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (SetChoice choiceId) currencyLabel numDecimals chosenNum
                    _ -> marloweActionInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (SetChoice choiceId) chosenNum
                ]
            , div [ class_ (ClassName "choice-error") ] error
            ]
        ]
          <> addButton
      )
  where
  mChoiceInfo = Map.lookup choiceName metadata.choiceInfo

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

  boundError (Bound from to) = showPretty from <> " and " <> showPretty to

  showPretty :: BigInteger -> String
  showPretty = showPrettyChoice (getChoiceFormat metadata choiceName)

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
              , marloweActionInput [ "mx-2", "flex-grow", "flex-shrink-0" ] (SetSlot <<< wrap) (unwrap slot)
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

marloweCurrencyInput :: forall p action. Array String -> (BigInteger -> action) -> String -> Int -> BigInteger -> HTML p action
marloweCurrencyInput classes f currencyLabel numDecimals current = currencyInput classes current currencyLabel numDecimals (Just <<< f <<< fromMaybe zero)

marloweActionInput :: forall p action. Array String -> (BigInteger -> action) -> BigInteger -> HTML p action
marloweActionInput classes f current = marloweCurrencyInput classes f "" 0 current

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
      , strong_ [ text (showPrettyChoice (getChoiceFormat metadata choiceName) chosenNum) ]
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
paymentToLines metadata slotInterval (Payment accountId payee money) = join $ unfoldAssets money (paymentToLine metadata slotInterval accountId payee)

paymentToLine :: forall p a. MetaData -> SlotInterval -> AccountId -> Payee -> Token -> BigInteger -> Array (HTML p a)
paymentToLine metadata (SlotInterval start end) accountId payee token money =
  [ span_
      [ text "The contract pays "
      , strong_ [ text (showPrettyMoney money) ]
      , text " units of "
      , strong_ [ renderPrettyToken token ]
      , text " to "
      , strong_ $ renderPrettyPayee metadata payee
      , text " from "
      , strong_ $ renderPrettyPayee metadata (Account accountId)
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

markdownHintWithTitle :: String -> String -> PlainHTML
markdownHintWithTitle title markdown =
  div_
    $ [ h4
          -- With min-w-max we define that the title should never break into
          -- a different line.
          [ classNames [ "no-margins", "text-lg", "font-semibold", "flex", "items-center", "pb-2", "min-w-max" ] ]
          [ Icon.icon Icon.HelpOutline [ "mr-1", "font-normal" ]
          , text title
          ]
      ]
    <> markdownToHTML markdown
