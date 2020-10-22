module Simulation where

import Auth (AuthRole(..), authStatusAuthRole)
import Control.Alternative (map, void, when, (<|>))
import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader (runReaderT)
import Data.Array (delete, filter, intercalate, snoc, sortWith)
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (_Just, assign, modifying, over, preview, to, use, view, (^.))
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, isNothing, maybe)
import Data.Newtype (wrap)
import Data.NonEmptyList.Extra (tailIfNotEmpty)
import Data.String (codePointFromChar)
import Data.String as String
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import FileEvents (readFileFromDragEvent)
import FileEvents as FileEvents
import Gist (Gist)
import Gists (GistAction(..), idPublishGist)
import Halogen (HalogenM, query)
import Halogen.Classes (aHorizontal, active, activeClasses, blocklyIcon, bold, closeDrawerIcon, codeEditor, expanded, infoIcon, jFlexStart, noMargins, panelSubHeader, panelSubHeaderMain, panelSubHeaderSide, plusBtn, pointer, sidebarComposer, smallBtn, spaceLeft, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, br_, button, div, em_, h6, h6_, img, input, label, li, option, p, p_, section, select, slot, small, span, strong_, text, ul)
import Halogen.HTML.Events (onClick, onSelectedIndexChange, onValueChange, onValueInput)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, disabled, enabled, href, placeholder, src, type_, value)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (Message(..), Query(..)) as Monaco
import Halogen.Monaco (monacoComponent)
import Halogen.SVG (Box(..), Length(..), Linecap(..), RGB(..), circle, clazz, cx, cy, d, fill, height, path, r, strokeLinecap, strokeWidth, svg, viewBox)
import Halogen.SVG as SVG
import Help (HelpContext(..), toHTML)
import Icons (Icon(..), icon)
import LocalStorage as LocalStorage
import Marlowe (SPParams_)
import Marlowe as Server
import Marlowe.Linter as Linter
import Marlowe.Monaco (updateAdditionalContext)
import Marlowe.Monaco as MM
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Bound(..), ChoiceId(..), Input(..), Party(..), PubKey, Token, emptyState, inBounds, showPrettyToken)
import Marlowe.Symbolic.Types.Request as MSReq
import Monaco (IMarker, isError, isWarning)
import Monaco (getModel, getMonaco, setTheme, setValue) as Monaco
import Network.RemoteData (RemoteData(..))
import Network.RemoteData as RemoteData
import Prelude (class Show, Unit, Void, bind, bottom, const, discard, eq, flip, identity, mempty, pure, show, unit, zero, ($), (-), (/=), (<), (<$>), (<<<), (<>), (=<<), (==), (>), (>=))
import Reachability (startReachabilityAnalysis)
import Servant.PureScript.Ajax (AjaxError)
import Servant.PureScript.Settings (SPSettings_)
import Simulation.BottomPanel (bottomPanel)
import Simulation.State (ActionInput(..), ActionInputId, _editorErrors, _editorWarnings, _executionState, _moveToAction, _pendingInputs, _possibleActions, _slot, _state, applyInput, emptyExecutionStateWithSlot, emptyMarloweState, hasHistory, mapPartiesActionInput, moveToSignificantSlot, moveToSlot, nextSignificantSlot, otherActionsParty, updateContractInState, updateMarloweState)
import Simulation.Types (Action(..), AnalysisState(..), State, WebData, _activeDemo, _analysisState, _authStatus, _bottomPanelView, _currentContract, _currentMarloweState, _editorKeybindings, _gistUrl, _createGistResult, _loadGistResult, _helpContext, _marloweState, _oldContract, _selectedHole, _showBottomPanel, _showErrorDetail, _showRightPanel, isContractValid)
import StaticData (marloweBufferLocalStorageKey)
import StaticData as StaticData
import Text.Pretty (genericPretty, pretty)
import Types (ChildSlots, _marloweEditorSlot)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

handleAction ::
  forall m.
  MonadEffect m =>
  MonadAff m =>
  SPSettings_ SPParams_ -> Action -> HalogenM State Action ChildSlots Void m Unit
handleAction settings Init = do
  checkAuthStatus settings
  editorSetTheme

handleAction _ (HandleEditorMessage (Monaco.TextChanged "")) = do
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState ""

handleAction _ (HandleEditorMessage (Monaco.TextChanged text)) = do
  assign _selectedHole Nothing
  liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey text
  updateContractInState text
  assign _activeDemo ""
  maybeExecutionState <- use (_currentMarloweState <<< _executionState)
  let
    state = maybe (emptyState zero) (\x -> x ^. _state) maybeExecutionState

    (Tuple markerData additionalContext) = Linter.markers state text
  markers <- query _marloweEditorSlot unit (Monaco.SetModelMarkers markerData identity)
  void $ traverse editorSetMarkers markers
  objects <- query _marloweEditorSlot unit (Monaco.GetObjects identity)
  case objects of
    Just { codeActionProvider: Just caProvider, completionItemProvider: Just ciProvider } -> pure $ updateAdditionalContext caProvider ciProvider additionalContext
    _ -> pure unit

handleAction _ (HandleDragEvent event) = liftEffect $ FileEvents.preventDefault event

handleAction _ (HandleDropEvent event) = do
  liftEffect $ FileEvents.preventDefault event
  contents <- liftAff $ readFileFromDragEvent event
  void $ editorSetValue contents
  updateContractInState contents

handleAction _ (MoveToPosition lineNumber column) = do
  void $ query _marloweEditorSlot unit (Monaco.SetPosition { column, lineNumber } unit)

handleAction _ (SelectEditorKeyBindings bindings) = do
  assign _editorKeybindings bindings
  void $ query _marloweEditorSlot unit (Monaco.SetKeyBindings bindings unit)

handleAction _ (LoadScript key) = do
  case preview (ix key) (Map.fromFoldable StaticData.marloweContracts) of
    Nothing -> pure unit
    Just contents -> do
      let
        prettyContents = case parseContract contents of
          Right pcon -> show $ pretty pcon
          Left _ -> contents
      editorSetValue prettyContents
      liftEffect $ LocalStorage.setItem marloweBufferLocalStorageKey prettyContents
      updateContractInState prettyContents
      resetContract
      assign _activeDemo key

handleAction _ (SetEditorText contents) = do
  editorSetValue contents
  updateContractInState contents

handleAction _ StartSimulation = do
  assign (_currentMarloweState <<< _executionState) (Just $ emptyExecutionStateWithSlot zero)
  moveToSlot zero

handleAction _ (MoveSlot slot) = do
  maybeExecutionState <- use (_currentMarloweState <<< _executionState)
  let
    slotGTcurrentSlot = maybe false (\x -> slot > (x ^. _slot)) maybeExecutionState
  significantSlot <- use (_marloweState <<< _Head <<< to nextSignificantSlot)
  when slotGTcurrentSlot do
    saveInitialState
    if slot >= (fromMaybe zero significantSlot) then
      moveToSignificantSlot slot
    else
      moveToSlot slot
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> editorSetValue (show $ genericPretty currContract)
      Nothing -> pure unit

handleAction _ (SetSlot slot) = assign (_currentMarloweState <<< _executionState <<< _Just <<< _possibleActions <<< _moveToAction) (Just $ MoveToSlot slot)

handleAction _ (AddInput input bounds) = do
  when validInput do
    saveInitialState
    applyInput ((flip snoc) input)
    mCurrContract <- use _currentContract
    case mCurrContract of
      Just currContract -> editorSetValue (show $ genericPretty currContract)
      Nothing -> pure unit
  where
  validInput = case input of
    (IChoice _ chosenNum) -> inBounds chosenNum bounds
    _ -> true

handleAction _ (RemoveInput input) = do
  updateMarloweState (over (_executionState <<< _Just <<< _pendingInputs) (delete input))
  currContract <- editorGetValue
  case currContract of
    Nothing -> pure unit
    Just contract -> updateContractInState contract

handleAction _ (SetChoice choiceId chosenNum) = updateMarloweState (over (_executionState <<< _Just <<< _possibleActions) (mapPartiesActionInput (updateChoice choiceId)))
  where
  updateChoice :: ChoiceId -> ActionInput -> ActionInput
  updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _)
    | wantedChoiceId == currentChoiceId = ChoiceInput choiceId bounds chosenNum

  updateChoice _ input = input

handleAction _ ResetSimulator = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  let
    newContract = fromMaybe mempty $ oldContract <|> currContract
  editorSetValue newContract
  resetContract

handleAction _ ResetContract = resetContract

handleAction _ Undo = do
  modifying _marloweState tailIfNotEmpty
  mCurrContract <- use _currentContract
  case mCurrContract of
    Just currContract -> editorSetValue (show $ genericPretty currContract)
    Nothing -> pure unit

handleAction _ (SelectHole hole) = assign _selectedHole hole

handleAction _ (ChangeSimulationView view) = do
  assign _bottomPanelView view
  assign _showBottomPanel true
  editorResize

handleAction _ (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

handleAction settings CheckAuthStatus = do
  checkAuthStatus settings

handleAction settings (GistAction subEvent) = pure unit

handleAction _ (ShowRightPanel val) = assign _showRightPanel val

handleAction _ (ShowBottomPanel val) = do
  assign _showBottomPanel val
  editorResize

handleAction _ (ShowErrorDetail val) = assign _showErrorDetail val

handleAction _ SetBlocklyCode = pure unit

handleAction settings AnalyseContract = do
  currContract <- use _currentContract
  maybeExecutionState <- use (_currentMarloweState <<< _executionState)
  let
    currState = maybe (emptyState zero) (\x -> x ^. _state) maybeExecutionState
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      assign _analysisState (WarningAnalysis Loading)
      response <- checkContractForWarnings contract currState
      assign _analysisState (WarningAnalysis response)
  where
  checkContractForWarnings contract state = runAjax $ (flip runReaderT) settings (Server.postMarloweanalysis (MSReq.Request { onlyAssertions: false, contract, state }))

handleAction settings AnalyseReachabilityContract = do
  currContract <- use _currentContract
  maybeExecutionState <- use (_currentMarloweState <<< _executionState)
  let
    currState = maybe (emptyState zero) (\x -> x ^. _state) maybeExecutionState
  case currContract of
    Nothing -> pure unit
    Just contract -> do
      newReachabilityAnalysisState <- startReachabilityAnalysis settings contract currState
      assign _analysisState (ReachabilityAnalysis newReachabilityAnalysisState)

getCurrentContract :: forall m. HalogenM State Action ChildSlots Void m String
getCurrentContract = do
  oldContract <- use _oldContract
  currContract <- editorGetValue
  pure $ fromMaybe mempty $ oldContract <|> currContract

checkAuthStatus :: forall m. MonadAff m => SPSettings_ SPParams_ -> HalogenM State Action ChildSlots Void m Unit
checkAuthStatus settings = do
  assign _authStatus Loading
  authResult <- runAjax $ runReaderT Server.getApiOauthStatus settings
  assign _authStatus authResult

runAjax ::
  forall m a.
  ExceptT AjaxError (HalogenM State Action ChildSlots Void m) a ->
  HalogenM State Action ChildSlots Void m (WebData a)
runAjax action = RemoteData.fromEither <$> runExceptT action

scrollHelpPanel :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
scrollHelpPanel =
  liftEffect do
    window <- Web.window
    document <- toDocument <$> W.document window
    mSidePanel <- WC.item 0 =<< D.getElementsByClassName "sidebar-composer" document
    mDocPanel <- WC.item 0 =<< D.getElementsByClassName "documentation-panel" document
    case mSidePanel, mDocPanel of
      Just sidePanel, Just docPanel -> do
        sidePanelHeight <- E.scrollHeight sidePanel
        docPanelHeight <- E.scrollHeight docPanel
        availableHeight <- E.clientHeight sidePanel
        let
          newScrollHeight =
            if sidePanelHeight < availableHeight then
              sidePanelHeight
            else
              sidePanelHeight - docPanelHeight - 120.0
        setScrollTop newScrollHeight sidePanel
      _, _ -> pure unit

editorSetTheme :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorSetTheme = void $ query _marloweEditorSlot unit (Monaco.SetTheme MM.daylightTheme.name unit)

editorResize :: forall state action msg m. HalogenM state action ChildSlots msg m Unit
editorResize = void $ query _marloweEditorSlot unit (Monaco.Resize unit)

editorSetValue :: forall state action msg m. String -> HalogenM state action ChildSlots msg m Unit
editorSetValue contents = void $ query _marloweEditorSlot unit (Monaco.SetText contents unit)

editorGetValue :: forall state action msg m. HalogenM state action ChildSlots msg m (Maybe String)
editorGetValue = query _marloweEditorSlot unit (Monaco.GetText identity)

saveInitialState :: forall m. MonadEffect m => HalogenM State Action ChildSlots Void m Unit
saveInitialState = do
  oldContract <- editorGetValue
  modifying _oldContract
    ( \x -> case x of
        Nothing -> Just $ fromMaybe "" oldContract
        _ -> x
    )

resetContract :: forall m. HalogenM State Action ChildSlots Void m Unit
resetContract = do
  newContract <- editorGetValue
  assign _marloweState $ NEL.singleton emptyMarloweState
  assign _oldContract Nothing
  updateContractInState $ fromMaybe "" newContract

editorSetMarkers :: forall m. MonadEffect m => Array IMarker -> HalogenM State Action ChildSlots Void m Unit
editorSetMarkers markers = do
  let
    warnings = filter (\{ severity } -> isWarning severity) markers

    trimHoles =
      map
        ( \marker ->
            let
              trimmedMessage =
                if String.take 6 marker.source == "Hole: " then
                  String.takeWhile (\c -> c /= codePointFromChar '\n') marker.message
                else
                  marker.message
            in
              marker { message = trimmedMessage }
        )
        warnings
  let
    errors = filter (\{ severity } -> isError severity) markers
  assign (_marloweState <<< _Head <<< _editorWarnings) trimHoles
  assign (_marloweState <<< _Head <<< _editorErrors) errors
  pure unit

render ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
render state =
  div []
    [ section [ classes [ panelSubHeader, aHorizontal ] ]
        [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
            [ a [ class_ (ClassName "editor-help"), onClick $ const $ Just $ ChangeHelpContext EditorHelp ]
                [ img [ src infoIcon, alt "info book icon" ] ]
            , div [ classes [ ClassName "demo-title", aHorizontal, jFlexStart ] ]
                [ div [ classes [ spaceLeft ] ]
                    [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Demos:" ]
                    ]
                ]
            , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
                (demoScriptLink <$> Array.fromFoldable (map fst StaticData.marloweContracts))
            , div [ class_ (ClassName "code-to-blockly-wrap") ]
                [ div [ class_ (ClassName "editor-options") ]
                    [ select
                        [ HTML.id_ "editor-options"
                        , class_ (ClassName "dropdown-header")
                        , onSelectedIndexChange (\idx -> SelectEditorKeyBindings <$> toEnum idx)
                        ]
                        (map keybindingItem (upFromIncluding bottom))
                    ]
                , button
                    [ classes [ smallBtn, ClassName "tooltip" ]
                    , onClick $ const $ Just $ SetBlocklyCode
                    , enabled isBlocklyEnabled
                    ]
                    [ span [ class_ (ClassName "tooltiptext") ] [ text "Send Contract to Blockly" ]
                    , img [ class_ (ClassName "blockly-btn-icon"), src blocklyIcon, alt "blockly logo" ]
                    ]
                ]
            ]
        , div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel) ] ]
            [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (not showRightPanel) ]
                [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
            , authButton state
            ]
        ]
    , section [ class_ (ClassName "code-panel") ]
        [ div [ classes (codeEditor $ state ^. _showBottomPanel) ]
            [ marloweEditor state ]
        , sidebar state
        ]
    , bottomPanel state
    ]
  where
  showRightPanel = state ^. _showRightPanel

  isBlocklyEnabled = view (_marloweState <<< _Head <<< _editorErrors <<< to Array.null) state

  demoScriptLink key =
    li [ state ^. _activeDemo <<< activeClasses (eq key) ]
      [ a [ onClick $ const $ Just $ LoadScript key ] [ text key ] ]

  keybindingItem item =
    if state ^. _editorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

marloweEditor ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
marloweEditor state = slot _marloweEditorSlot unit component unit (Just <<< HandleEditorMessage)
  where
  setup editor = do
    mContents <- liftEffect $ LocalStorage.getItem StaticData.marloweBufferLocalStorageKey
    let
      contents = fromMaybe initialContents mContents
    model <- liftEffect $ Monaco.getModel editor
    liftEffect do
      Monaco.setValue model contents
      -- Since the Simulation Tab is viewed before the Haskell tab we need to set the correct editor theme when things have been loaded
      monaco <- Monaco.getMonaco
      Monaco.setTheme monaco MM.daylightTheme.name

  component = monacoComponent $ MM.settings setup

  initialContents = fromMaybe "?contract" $ Array.head $ map snd StaticData.marloweContracts

sidebar ::
  forall p.
  State ->
  HTML p Action
sidebar state =
  let
    showRightPanel = state ^. _showRightPanel
  in
    aside [ classes [ sidebarComposer, expanded showRightPanel ] ]
      [ div [ classes [ aHorizontal, ClassName "transaction-composer" ] ]
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
transactionComposer state
  | isNothing (state ^. (_marloweState <<< _Head <<< _executionState)) =
    div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
      [ ul [ class_ (ClassName "participants") ]
          [ text "Simulation has not started yet" ]
      , div [ class_ (ClassName "transaction-btns") ]
          [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              [ li [ classes [ bold, pointer ] ]
                  [ a
                      [ onClick $ const $ Just StartSimulation ]
                      [ text "Start simulation" ]
                  ]
              ]
          ]
      ]
  | true =
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

    possibleActions = view (_marloweState <<< _Head <<< _executionState <<< _Just <<< _possibleActions <<< _Newtype) state

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
    if isEnabled && inFuture then
      [ button
          [ classes [ plusBtn, smallBtn, ClassName "align-top" ]
          , onClick $ const $ Just $ MoveSlot slot
          ]
          [ text "+" ]
      ]
    else
      []

  inFuture = maybe false (\x -> x.slot < slot) (state ^. (_currentMarloweState <<< _executionState))

  error = if inFuture then [] else [ text boundsError ]

  boundsError = "The slot must be more than the current slot " <> (state ^. (_currentMarloweState <<< _executionState <<< _Just <<< _slot <<< to show))

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
  , b_ [ spanText (show money) ]
  , spanText " units of "
  , b_ [ spanText (showPrettyToken tok) ]
  , spanText " into Account "
  , b_ [ spanText (show accountOwner) ]
  , spanText " as "
  , b_ [ spanText (show party) ]
  ]

authButton :: forall p. State -> HTML p Action
authButton state =
  let
    authStatus = state ^. (_authStatus <<< to (map (view authStatusAuthRole)))
  in
    case authStatus of
      Failure _ ->
        button
          [ idPublishGist
          , classes []
          ]
          [ text "Failed to login" ]
      Success Anonymous ->
        div [ class_ (ClassName "auth-button-container") ]
          [ a
              [ idPublishGist
              , classes [ ClassName "auth-button" ]
              , href "/api/oauth/github"
              ]
              [ text "Save to GitHub"
              ]
          ]
      Success GithubUser -> gistSection state
      Loading ->
        button
          [ idPublishGist
          , classes []
          , disabled true
          ]
          [ icon Spinner ]
      NotAsked ->
        button
          [ idPublishGist
          , classes []
          , disabled true
          ]
          [ icon Spinner ]

spinner :: forall p. HTML p Action
spinner =
  svg [ clazz (ClassName "spinner"), SVG.width (Px 65), height (Px 65), viewBox (Box { x: 0, y: 0, width: 66, height: 66 }) ]
    [ circle [ clazz (ClassName "path"), fill SVG.None, strokeWidth 6, strokeLinecap Round, cx (Length 33.0), cy (Length 33.0), r (Length 30.0) ] [] ]

arrowDown :: forall p. HTML p Action
arrowDown =
  svg [ clazz (ClassName "arrow-down"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#832dc4"), d "M19.92,12.08L12,20L4.08,12.08L5.5,10.67L11,16.17V2H13V16.17L18.5,10.66L19.92,12.08M12,20H2V22H22V20H12Z" ] [] ]

arrowUp :: forall p. HTML p Action
arrowUp =
  svg [ clazz (ClassName "arrow-up"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#832dc4"), d "M4.08,11.92L12,4L19.92,11.92L18.5,13.33L13,7.83V22H11V7.83L5.5,13.33L4.08,11.92M12,4H22V2H2V4H12Z" ] [] ]

errorIcon :: forall p. HTML p Action
errorIcon =
  svg [ clazz (ClassName "error-icon"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#ff0000"), d "M13,13H11V7H13M12,17.3A1.3,1.3 0 0,1 10.7,16A1.3,1.3 0 0,1 12,14.7A1.3,1.3 0 0,1 13.3,16A1.3,1.3 0 0,1 12,17.3M15.73,3H8.27L3,8.27V15.73L8.27,21H15.73L21,15.73V8.27L15.73,3Z" ] [] ]

gistButtonIcon :: forall p. HTML p Action -> Either String (RemoteData AjaxError Gist) -> HTML p Action
gistButtonIcon _ (Left _) = errorIcon

gistButtonIcon _ (Right (Failure _)) = errorIcon

gistButtonIcon arrow (Right (Success _)) = arrow

gistButtonIcon _ (Right Loading) = spinner

gistButtonIcon arrow (Right NotAsked) = arrow

gistInput :: forall p. State -> Either String (RemoteData AjaxError Gist) -> HTML p Action
gistInput state (Left _) =
  input
    [ HTML.type_ InputText
    , classes [ ClassName "form-control", ClassName "py-0", ClassName "error" ]
    , HTML.id_ "github-input"
    , placeholder "Gist ID"
    , value (state ^. _gistUrl <<< to (fromMaybe ""))
    , onValueInput $ Just <<< GistAction <<< SetGistUrl
    ]

gistInput state (Right (Failure _)) =
  input
    [ HTML.type_ InputText
    , classes [ ClassName "form-control", ClassName "py-0", ClassName "error" ]
    , HTML.id_ "github-input"
    , placeholder "Gist ID"
    , value (state ^. _gistUrl <<< to (fromMaybe ""))
    , onValueInput $ Just <<< GistAction <<< SetGistUrl
    ]

gistInput state _ =
  input
    [ HTML.type_ InputText
    , classes [ ClassName "form-control", ClassName "py-0" ]
    , HTML.id_ "github-input"
    , placeholder "Gist ID"
    , value (state ^. _gistUrl <<< to (fromMaybe ""))
    , onValueInput $ Just <<< GistAction <<< SetGistUrl
    ]

gistSection :: forall p. State -> HTML p Action
gistSection state =
  div [ classes [ ClassName "github-gist-panel", aHorizontal, expanded (state ^. _showRightPanel) ] ]
    [ div [ classes [ ClassName "input-group-text", ClassName "upload-btn", ClassName "tooltip" ], onClick $ const $ Just $ GistAction PublishGist ]
        [ span [ class_ (ClassName "tooltiptext") ] [ publishTooltip publishStatus ]
        , gistButtonIcon arrowUp publishStatus
        ]
    , label [ classes [ ClassName "sr-only", active ], HTML.for "github-input" ] [ text "Enter Github Gist" ]
    , div [ classes (map ClassName [ "input-group", "mb-2", "mr-sm-2" ]) ]
        [ gistInput state loadStatus
        , div [ class_ (ClassName "input-group-append") ]
            [ div
                [ classes [ ClassName "input-group-text", ClassName "download-btn", ClassName "tooltip" ]
                , onClick $ const $ Just $ GistAction LoadGist
                ]
                [ span [ class_ (ClassName "tooltiptext") ] [ loadTooltip loadStatus ]
                , gistButtonIcon arrowDown loadStatus
                ]
            ]
        ]
    ]
  where
  publishStatus = state ^. _createGistResult <<< to Right

  loadStatus = state ^. _loadGistResult

  publishTooltip (Left _) = text "Failed to publish gist"

  publishTooltip (Right (Failure _)) = text "Failed to publish gist"

  publishTooltip _ = text "Publish To Github Gist"

  loadTooltip (Left e) = text "Failed to load gist"

  loadTooltip (Right (Failure _)) = text "Failed to load gist"

  loadTooltip _ = text "Load From Github Gist"
