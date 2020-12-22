module SimulationPage.View where

import Control.Alternative (map, void, when, (<*>), (<|>))
import Control.Monad.Except (ExceptT, runExceptT, runExcept)
import Control.Monad.Reader (runReaderT)
import Data.Array (delete, filter, intercalate, snoc, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Decimal (truncated, fromNumber)
import Data.Decimal as Decimal
import Data.Either (Either(..), hush)
import Data.Enum (toEnum, upFromIncluding)
import Data.EuclideanRing ((*))
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (assign, has, modifying, only, over, preview, set, to, use, view, (^.))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty as NEL
import Data.List.Types (List(..), NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.NonEmptyList.Extra (tailIfNotEmpty)
import Data.RawJson (RawJson(..))
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (for_, traverse)
import Data.Tuple (Tuple(..), snd)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Foreign.Generic (ForeignError, decode)
import Foreign.JSON (parseJSON)
import Halogen (HalogenM, get, modify_, query)
import Halogen.Classes (aHorizontal, bold, closeDrawerIcon, codeEditor, expanded, fullHeight, group, infoIcon, noMargins, panelSubHeaderSide, plusBtn, pointer, scroll, sidebarComposer, smallBtn, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, br_, button, div, em_, h6, h6_, img, input, li, option, p, p_, section, select, slot, small, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick, onSelectedIndexChange, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, src, type_, value)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (Settings, monacoComponent)
import Help (HelpContext(..), toHTML)
import Language.Haskell.Monaco (languageExtensionPoint, refLabel)
import LocalStorage as LocalStorage
import MainFrame.Types (ChildSlots, _hasUnsavedChanges', _marloweEditorSlot)
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Holes (fromTerm)
import Marlowe.Linter as Linter
import Marlowe.Monaco (daylightTheme, updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Bound(..), ChoiceId(..), Input(..), Party(..), PubKey, Token, emptyState, inBounds)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (Editor, IMarker, isError, isWarning)
import Monaco (getModel, getMonaco, setTheme, setValue) as Monaco
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (class Show, Unit, Void, bind, bottom, const, discard, eq, flip, identity, mempty, pure, show, unit, zero, ($), (-), (/=), (<), (<$>), (<<<), (<>), (=<<), (==), (>=))
import Pretty (renderPrettyParty, renderPrettyToken, showPrettyMoney)
import Prim.TypeError (class Warn, Text)
import Projects.Types (Lang(..))
import Servant.PureScript.Ajax (AjaxError, errorToString)
import Servant.PureScript.Settings (SPSettings_)
import SimulationPage.BottomPanel (bottomPanel)
import SimulationPage.Types (Action(..), ActionInput(..), ActionInputId(..), ExecutionState(..), Parties(..), State, _SimulationNotStarted, _SimulationRunning, _bottomPanelView, _contract, _currentContract, _currentMarloweState, _editorErrors, _editorKeybindings, _editorWarnings, _executionState, _helpContext, _initialSlot, _marloweState, _moveToAction, _oldContract, _pendingInputs, _possibleActions, _selectedHole, _showBottomPanel, _showRightPanel, _slot, _source, emptyExecutionStateWithSlot, emptyMarloweState, isContractValid, mapPartiesActionInput, otherActionsParty)
import Simulator (applyInput, getAsMuchStateAsPossible, hasHistory, inFuture, moveToSignificantSlot, moveToSlot, nextSignificantSlot, updateContractInState, updateMarloweState)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (genericPretty, pretty)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

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
    ( [ sendToBlocklyButton state
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

marloweEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
marloweEditor state = slot _marloweEditorSlot unit component unit (const Nothing)
  where
  -- FIXME: probably dont use local storage nor empty ?contract... see what a good default should be
  setup editor = do
    mContents <- liftEffect $ LocalStorage.getItem StaticData.marloweBufferLocalStorageKey
    let
      contents = fromMaybe "?contract" (mContents <|> Map.lookup "Example" StaticData.marloweContracts)
    model <- liftEffect $ Monaco.getModel editor
    liftEffect do
      Monaco.setValue model contents
      -- Since the Simulation Tab is viewed before the Haskell tab we need to set the correct editor theme when things have been loaded
      monaco <- Monaco.getMonaco
      Monaco.setTheme monaco MM.daylightTheme.name

  component = monacoComponent $ settings setup

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
