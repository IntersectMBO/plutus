module SimulationPage.View where

import Control.Alternative (map, (<|>))
import Data.Array (intercalate, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (has, only, to, view, (^.))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.Tuple (Tuple(..), snd)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen (RefLabel(..))
import Halogen.Classes (aHorizontal, bold, closeDrawerIcon, codeEditor, expanded, fullHeight, group, infoIcon, noMargins, panelSubHeaderSide, plusBtn, pointer, scroll, sidebarComposer, smallBtn, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, br_, button, div, em_, h6, h6_, img, input, li, p, p_, section, slot, small, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, src, type_, value)
import Halogen.Monaco (Settings, monacoComponent)
import Help (HelpContext(..), toHTML)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _simulatorEditorSlot)
import Marlowe.Monaco (daylightTheme, languageExtensionPoint)
import Marlowe.Monaco as MM
import Marlowe.Semantics (AccountId, Bound(..), ChoiceId(..), Input(..), Party(..), PubKey, Token, inBounds)
import Monaco (Editor)
import Monaco as Monaco
import Prelude (class Show, Unit, bind, const, discard, show, unit, ($), (<<<), (<>), (==))
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import Projects.Types (Lang(..))
import SimulationPage.BottomPanel (bottomPanel)
import SimulationPage.Types (Action(..), ActionInput(..), ActionInputId, ExecutionState(..), State, _SimulationRunning, _currentMarloweState, _editorErrors, _executionState, _helpContext, _marloweState, _possibleActions, _showBottomPanel, _showRightPanel, _slot, isContractValid, otherActionsParty)
import Simulator (hasHistory, inFuture)
import StaticData as StaticData

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div [ classes [ fullHeight, scroll, ClassName "simulation-panel" ] ]
    [ section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ marloweEditor state ]
        , sidebar state
        ]
    , bottomPanel state
    ]
  where
  showRightPanel = state ^. _showRightPanel

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

-- FIXME while doing the refactor this settigns were colliding with the marlowe. Delete
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

sidebar ::
  forall p.
  State ->
  HTML p Action
sidebar state =
  let
    showRightPanel = state ^. _showRightPanel
  in
    aside [ classes [ sidebarComposer, expanded showRightPanel ] ]
      [ div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel), ClassName "drawer-icon-container" ] ]
          [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (not showRightPanel) ]
              [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
          ]
      , div [ classes [ aHorizontal, ClassName "transaction-composer" ] ]
          [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
              [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Available Actions" ] ]
          , a [ onClick $ const $ Just $ ChangeHelpContext AvailableActionsHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
          ]
      , transactionComposer state
      , article [ class_ (ClassName "documentation-panel") ]
          (toHTML (state ^. _helpContext))
      ]

transactionComposer ::
  forall p.
  State ->
  HTML p Action
transactionComposer state = case view (_marloweState <<< _Head <<< _executionState) state of
  SimulationNotStarted { initialSlot } ->
    div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
      [ ul_
          [ h6
              [ classes
                  [ ClassName "input-composer-heading"
                  , noMargins
                  ]
              ]
              [ text "Simulation has not started yet" ]
          , div [ classes [ ClassName "slot-input", ClassName "initial-slot-input" ] ]
              [ spanText "Initial slot:"
              , marloweActionInput true (SetInitialSlot <<< wrap) initialSlot
              ]
          ]
      , div [ class_ (ClassName "transaction-btns") ]
          [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              [ li [ classes [ bold, pointer ] ]
                  [ a [ onClick $ const $ Just StartSimulation ]
                      [ text "Start simulation" ]
                  ]
              ]
          ]
      ]
  SimulationRunning _ ->
    div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
      [ ul [ class_ (ClassName "participants") ]
          if (Map.isEmpty possibleActions) then
            [ text "No valid inputs can be added to the transaction" ]
          else
            (actionsForParties possibleActions)
      , div [ class_ (ClassName "transaction-btns") ]
          [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              [ li [ classes [ bold, pointer ] ]
                  [ a
                      [ onClick $ const
                          $ if hasHistory state then
                              Just Undo
                            else
                              Nothing
                      , class_ (Classes.disabled $ not isEnabled)
                      ]
                      [ text "Undo" ]
                  ]
              , li [ classes [ bold, pointer ] ]
                  [ a
                      [ onClick $ const
                          $ if hasHistory state then
                              Just ResetSimulator
                            else
                              Nothing
                      , class_ (Classes.disabled $ not isEnabled)
                      ]
                      [ text "Reset" ]
                  ]
              ]
          ]
      ]
  where
  isEnabled = isContractValid state

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
  actionsForParties m = map (\(Tuple k v) -> participant state isEnabled k (vs v)) (sortParties (kvs m))

participant ::
  forall p.
  State ->
  Boolean ->
  Party ->
  Array ActionInput ->
  HTML p Action
participant state isEnabled party actionInputs =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    ( [ h6_ [ em_ title ] ]
        <> (map (inputItem state isEnabled partyName) actionInputs)
    )
  where
  title =
    if party == otherActionsParty then
      [ text "Other Actions" ]
    else
      [ text "Participant ", strong_ [ text partyName ] ]

  partyName = case party of
    (PK name) -> name
    (Role name) -> name

inputItem ::
  forall p.
  State ->
  Boolean ->
  PubKey ->
  ActionInput ->
  HTML p Action
inputItem _ isEnabled person (DepositInput accountId party token value) =
  div [ classes [ aHorizontal ] ]
    [ p_ (renderDeposit accountId party token value)
    , div [ class_ (ClassName "align-top") ]
        [ button
            [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
            , enabled isEnabled
            , onClick $ const $ Just
                $ AddInput (IDeposit accountId party token value) []
            ]
            [ text "+" ]
        ]
    ]

inputItem _ isEnabled person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "choice-input") ]
              [ spanText "Choice "
              , b_ [ spanText (show choiceName <> ":") ]
              , br_
              , spanText "Choose value "
              , marloweActionInput isEnabled (SetChoice choiceId) chosenNum
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if isEnabled && inBounds chosenNum bounds then
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

inputItem _ isEnabled person NotifyInput =
  li
    [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_ [ text "Notify Contract" ]
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled), ClassName "align-top" ]
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput INotify []
        ]
        [ text "+" ]
    ]

inputItem state isEnabled person (MoveToSlot slot) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    ( [ div []
          [ p [ class_ (ClassName "slot-input") ]
              [ spanText "Move to slot "
              , marloweActionInput isEnabled (SetSlot <<< wrap) slot
              ]
          , p [ class_ (ClassName "choice-error") ] error
          ]
      ]
        <> addButton
    )
  where
  addButton =
    if isEnabled && inFuture state slot then
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

marloweActionInput :: forall p a. Show a => Boolean -> (BigInteger -> Action) -> a -> HTML p Action
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
