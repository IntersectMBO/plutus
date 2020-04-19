module Simulation where

import Auth (AuthRole(..), authStatusAuthRole)
import Control.Alternative (map)
import Data.Array (foldr, intercalate, (:))
import Data.Array as Array
import Data.BigInteger (BigInteger, fromString, fromInt)
import Data.Either (Either(..))
import Data.Enum (toEnum, upFromIncluding)
import Data.HeytingAlgebra (not, (&&))
import Data.Lens (to, view, (^.))
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Gist (Gist)
import Gists (GistAction(..), idPublishGist)
import Halogen.Classes (aHorizontal, active, activeClasses, blocklyIcon, bold, closeDrawerIcon, codeEditor, expanded, infoIcon, jFlexStart, minusBtn, noMargins, panelSubHeader, panelSubHeaderMain, panelSubHeaderSide, plusBtn, pointer, smallBtn, spaceLeft, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, a, article, aside, b_, button, div, em_, h2, h6, h6_, img, input, label, li, li_, option, p, p_, section, select, slot, small, small_, span, strong_, text, ul, ul_)
import Halogen.HTML.Events (onClick, onSelectedIndexChange, onValueChange, onValueInput)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, disabled, enabled, href, placeholder, src, type_, value)
import Halogen.HTML.Properties as HTML
import Halogen.Monaco (monacoComponent)
import Halogen.SVG (Box(..), Length(..), Linecap(..), RGB(..), circle, clazz, cx, cy, d, fill, height, path, r, strokeLinecap, strokeWidth, svg, viewBox)
import Halogen.SVG as SVG
import Help (toHTML)
import Icons (Icon(..), icon)
import LocalStorage as LocalStorage
import Marlowe.Monaco as MM
import Marlowe.Semantics (AccountId(..), Bound(..), ChoiceId(..), Input(..), Party, PubKey, Token, TransactionError, inBounds)
import Monaco as Monaco
import Network.RemoteData (RemoteData(..))
import Prelude (class Show, bind, bottom, const, discard, eq, mempty, show, unit, ($), (<$>), (<<<), (<>), (==), (>))
import Servant.PureScript.Ajax (AjaxError)
import Simulation.BottomPanel (isContractValid)
import StaticData as StaticData
import Types (ActionInput(..), ActionInputId, ChildSlots, FrontendState, HAction(..), HelpContext(..), _Head, _activeMarloweDemo, _authStatus, _createGistResult, _gistUrl, _helpContext, _loadGistResult, _marloweEditorKeybindings, _marloweEditorSlot, _marloweState, _pendingInputs, _possibleActions, _showRightPanel, _slot)

render ::
  forall m.
  MonadAff m =>
  FrontendState ->
  Array (ComponentHTML HAction ChildSlots m)
render state =
  [ section [ classes [ panelSubHeader, aHorizontal ] ]
      [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
          [ div [ classes [ ClassName "demo-title", aHorizontal, jFlexStart ] ]
              [ div [ classes [ ClassName "demos", spaceLeft ] ]
                  [ small_ [ text "Demos:" ]
                  ]
              ]
          , ul [ classes [ ClassName "demo-list", aHorizontal ] ]
              (demoScriptLink <$> Array.fromFoldable (map fst StaticData.marloweContracts))
          , div [ class_ (ClassName "code-to-blockly-wrap") ]
              [ div [ class_ (ClassName "editor-options") ]
                  [ select
                      [ HTML.id_ "editor-options"
                      , class_ (ClassName "dropdown-header")
                      , onSelectedIndexChange (\idx -> MarloweSelectEditorKeyBindings <$> toEnum idx)
                      ]
                      (map keybindingItem (upFromIncluding bottom))
                  ]
              , button
                  [ classes [ smallBtn, ClassName "tooltip" ]
                  , onClick $ const $ Just $ SetBlocklyCode
                  , enabled (isContractValid state)
                  ]
                  [ span [ class_ (ClassName "tooltiptext") ] [ text "Send Contract to Blockly" ]
                  , img [ class_ (ClassName "blockly-btn-icon"), src blocklyIcon, alt "blockly logo" ]
                  ]
              ]
          ]
      , div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel) ] ] [ authButton state ]
      ]
  , section [ class_ (ClassName "code-panel") ]
      [ div [ classes (codeEditor state) ]
          [ marloweEditor state ]
      , sidebar state
      ]
  ]
  where
  demoScriptLink key =
    li [ state ^. _activeMarloweDemo <<< activeClasses (eq key) ]
      [ a [ onClick $ const $ Just $ LoadMarloweScript key ] [ text key ] ]

  keybindingItem item =
    if state ^. _marloweEditorKeybindings == item then
      option [ class_ (ClassName "selected-item"), HTML.value (show item) ] [ text $ show item ]
    else
      option [ HTML.value (show item) ] [ text $ show item ]

marloweEditor ::
  forall m.
  MonadAff m =>
  FrontendState ->
  ComponentHTML HAction ChildSlots m
marloweEditor state = slot _marloweEditorSlot unit component unit (Just <<< MarloweHandleEditorMessage)
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

  initialContents = fromMaybe "" $ Array.head $ map fst StaticData.marloweContracts

sidebar ::
  forall p.
  FrontendState ->
  HTML p HAction
sidebar state =
  let
    showRightPanel = state ^. _showRightPanel
  in
    aside [ classes [ (ClassName "sidebar-composer"), expanded showRightPanel ] ]
      [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (not showRightPanel) ]
          [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
      , div [ class_ aHorizontal ]
          [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
              [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Input Composer" ] ]
          , a [ onClick $ const $ Just $ ChangeHelpContext InputComposerHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
          ]
      , inputComposer state
      , div [ classes [ aHorizontal, ClassName "transaction-composer" ] ]
          [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
              [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Transaction Composer" ] ]
          , a [ onClick $ const $ Just $ ChangeHelpContext TransactionComposerHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
          ]
      , transactionComposer state
      , article [ class_ (ClassName "documentation-panel") ]
          (toHTML (state ^. _helpContext))
      ]

inputComposer ::
  forall p.
  FrontendState ->
  HTML p HAction
inputComposer state =
  div [ classes [ ClassName "input-composer", ClassName "composer" ] ]
    [ ul [ class_ (ClassName "participants") ]
        if (Map.isEmpty possibleActions) then
          [ text "No valid inputs can be added to the transaction" ]
        else
          (actionsForPeople possibleActions)
    ]
  where
  isEnabled = isContractValid state

  possibleActions = view (_marloweState <<< _Head <<< _possibleActions) state

  kvs :: forall k v. Map k v -> Array (Tuple k v)
  kvs = Map.toUnfoldable

  vs :: forall k v. Map k v -> Array v
  vs m = map snd (kvs m)

  lastKey :: Maybe (Maybe PubKey)
  lastKey = map (\x -> x.key) (Map.findMax possibleActions)

  people :: forall v. Array (Tuple (Maybe String) v) -> Array (Tuple String v)
  people = foldr f mempty
    where
    f (Tuple (Just k) v) acc = (Tuple k v) : acc

    f _ acc = acc

  actionsForPeople :: Map (Maybe PubKey) (Map ActionInputId ActionInput) -> Array (HTML p HAction)
  actionsForPeople m = map (\(Tuple k v) -> participant isEnabled k (vs v)) (people (kvs m))

participant ::
  forall p.
  Boolean ->
  PubKey ->
  Array ActionInput ->
  HTML p HAction
participant isEnabled person actionInputs =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    ( [ h6_ [ em_ [ text "Participant ", strong_ [ text person ] ] ] ]
        <> (map (inputItem isEnabled person) actionInputs)
    )

inputItem ::
  forall p.
  Boolean ->
  PubKey ->
  ActionInput ->
  HTML p HAction
inputItem isEnabled person (DepositInput accountId party token value) =
  div [ classes [ aHorizontal ] ]
    [ p_ (renderDeposit accountId party token value)
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput (Just person) (IDeposit accountId party token value) []
        ]
        [ text "+" ]
    ]

inputItem isEnabled person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  div
    [ classes [ aHorizontal, ClassName "flex-wrap" ] ]
    [ div []
        [ p [ class_ (ClassName "choice-input") ]
            [ spanText "Choice "
            , b_ [ spanText (show choiceName) ]
            , spanText ": Choose value "
            , marloweActionInput isEnabled (SetChoice choiceId) chosenNum
            ]
        , p [ class_ (ClassName "choice-error") ] error
        ]
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
        , enabled (isEnabled && inBounds chosenNum bounds)
        , onClick $ const $ Just
            $ AddInput (Just person) (IChoice (ChoiceId choiceName choiceOwner) chosenNum) bounds
        ]
        [ text "+" ]
    ]
  where
  error = if inBounds chosenNum bounds then [] else [ text boundsError ]

  boundsError = "Choice must be between " <> intercalate " or " (map boundError bounds)

  boundError (Bound from to) = show from <> " and " <> show to

inputItem isEnabled person NotifyInput =
  li
    [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_ [ text "Notify Contract" ]
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput (Just person) INotify []
        ]
        [ text "+" ]
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

renderDeposit :: forall p. AccountId -> Party -> Token -> BigInteger -> Array (HTML p HAction)
renderDeposit (AccountId accountNumber accountOwner) party tok money =
  [ spanText "Deposit "
  , b_ [ spanText (show money) ]
  , spanText " units of "
  , b_ [ spanText (show tok) ]
  , spanText " into Account "
  , b_ [ spanText (show accountOwner <> " (" <> show accountNumber <> ")") ]
  , spanText " as "
  , b_ [ spanText (show party) ]
  ]

transactionComposer ::
  forall p.
  FrontendState ->
  HTML p HAction
transactionComposer state =
  div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
    [ ul [ class_ (ClassName "participants") ]
        if Array.null pendingInputs then
          [ text "Empty transaction" ]
        else
          [ transaction state isEnabled ]
    , div [ class_ (ClassName "transaction-btns") ]
        [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
            [ li [ classes [ bold, pointer ] ]
                [ a
                    [ onClick
                        $ if hasHistory state then
                            Just <<< const Undo
                          else
                            const Nothing
                    , class_ (Classes.disabled $ not isEnabled)
                    ]
                    [ text "Undo" ]
                ]
            , li [ classes [ bold, pointer ] ]
                [ a
                    [ onClick
                        $ if hasHistory state then
                            Just <<< const ResetSimulator
                          else
                            const Nothing
                    , class_ (Classes.disabled $ not isEnabled)
                    ]
                    [ text "Reset" ]
                ]
            , li [ classes [ bold, pointer ] ]
                [ a
                    [ onClick
                        $ if isEnabled then
                            Just <<< const NextSlot
                          else
                            const Nothing
                    , class_ (Classes.disabled $ not isEnabled)
                    ]
                    [ text $ "Next Block (" <> show currentBlock <> ")" ]
                ]
            , li_
                [ button
                    [ onClick $ Just <<< const ApplyTransaction
                    , enabled isEnabled
                    , class_ (Classes.disabled $ not isEnabled)
                    ]
                    [ text "Apply" ]
                ]
            ]
        ]
    ]
  where
  currentBlock = state ^. (_marloweState <<< _Head <<< _slot)

  isEnabled = isContractValid state

  pendingInputs = state ^. (_marloweState <<< _Head <<< _pendingInputs)

transaction ::
  forall p.
  FrontendState ->
  Boolean ->
  HTML p HAction
transaction state isEnabled =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    [ ul
        []
        (map (transactionRow state isEnabled) (state ^. (_marloweState <<< _Head <<< _pendingInputs)))
    ]

transactionRow ::
  forall p.
  FrontendState ->
  Boolean ->
  Tuple Input (Maybe PubKey) ->
  HTML p HAction
transactionRow state isEnabled (Tuple input@(IDeposit (AccountId accountNumber accountOwner) party token money) person) =
  li [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_
        [ text "Deposit "
        , strong_ [ text (show money) ]
        , text " units of "
        , strong_ [ text (show token) ]
        , text " into account "
        , strong_ [ text (show accountOwner <> " (" <> show accountNumber <> ")") ]
        , text " as "
        , strong_ [ text (show party) ]
        ]
    , button
        [ classes [ minusBtn, smallBtn, bold, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just $ RemoveInput person input
        ]
        [ text "-" ]
    ]

transactionRow state isEnabled (Tuple input@(IChoice (ChoiceId choiceName choiceOwner) chosenNum) person) =
  li [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_
        [ text "Participant "
        , strong_ [ text (show choiceOwner) ]
        , text " chooses the value "
        , strong_ [ text (show chosenNum) ]
        , text " for choice with id "
        , strong_ [ text (show choiceName) ]
        ]
    , button
        [ classes [ minusBtn, smallBtn, bold, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just $ RemoveInput person input
        ]
        [ text "-" ]
    ]

transactionRow state isEnabled (Tuple INotify person) =
  li [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_
        [ text "Notification"
        ]
    , button
        [ classes [ minusBtn, smallBtn, bold, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just $ RemoveInput person INotify
        ]
        [ text "-" ]
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
          , ClassName "transaction-composer"
          ]
      ]
      ( [ h2 [] [ text "The transaction is invalid:" ] ]
          <> printTransError error
      )
  ]

authButton :: forall p. FrontendState -> HTML p HAction
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
          [ text "Failure" ]
      Success Anonymous ->
        a
          [ idPublishGist
          , classes [ ClassName "auth-button" ]
          , href "/api/oauth/github"
          ]
          [ text "Save to GitHub"
          ]
      Success GithubUser -> gist state
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

spinner :: forall p. HTML p HAction
spinner =
  svg [ clazz (ClassName "spinner"), SVG.width (Px 65), height (Px 65), viewBox (Box { x: 0, y: 0, width: 66, height: 66 }) ]
    [ circle [ clazz (ClassName "path"), fill SVG.None, strokeWidth 6, strokeLinecap Round, cx (Length 33.0), cy (Length 33.0), r (Length 30.0) ] [] ]

arrowDown :: forall p. HTML p HAction
arrowDown =
  svg [ clazz (ClassName "arrow-down"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#832dc4"), d "M19.92,12.08L12,20L4.08,12.08L5.5,10.67L11,16.17V2H13V16.17L18.5,10.66L19.92,12.08M12,20H2V22H22V20H12Z" ] [] ]

arrowUp :: forall p. HTML p HAction
arrowUp =
  svg [ clazz (ClassName "arrow-up"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#832dc4"), d "M4.08,11.92L12,4L19.92,11.92L18.5,13.33L13,7.83V22H11V7.83L5.5,13.33L4.08,11.92M12,4H22V2H2V4H12Z" ] [] ]

errorIcon :: forall p. HTML p HAction
errorIcon =
  svg [ clazz (ClassName "error-icon"), SVG.width (Px 20), height (Px 20), viewBox (Box { x: 0, y: 0, width: 24, height: 24 }) ]
    [ path [ fill (Hex "#ff0000"), d "M13,13H11V7H13M12,17.3A1.3,1.3 0 0,1 10.7,16A1.3,1.3 0 0,1 12,14.7A1.3,1.3 0 0,1 13.3,16A1.3,1.3 0 0,1 12,17.3M15.73,3H8.27L3,8.27V15.73L8.27,21H15.73L21,15.73V8.27L15.73,3Z" ] [] ]

gistButtonIcon :: forall p. HTML p HAction -> Either String (RemoteData AjaxError Gist) -> HTML p HAction
gistButtonIcon _ (Left _) = errorIcon

gistButtonIcon _ (Right (Failure _)) = errorIcon

gistButtonIcon arrow (Right (Success _)) = arrow

gistButtonIcon _ (Right Loading) = spinner

gistButtonIcon arrow (Right NotAsked) = arrow

gistInput :: forall p. FrontendState -> Either String (RemoteData AjaxError Gist) -> HTML p HAction
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

gist :: forall p. FrontendState -> HTML p HAction
gist state =
  div [ classes [ ClassName "github-gist-panel", aHorizontal ] ]
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

  loadTooltip (Left _) = text "Failed to load gist"

  loadTooltip (Right (Failure _)) = text "Failed to load gist"

  loadTooltip _ = text "Load From Github Gist"
