module Wallet where

import Prelude hiding (div)
import Control.Alt ((<|>))
import Control.Monad.State (class MonadState)
import Data.Array (concatMap, delete, drop, fold, foldMap, snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Foldable (foldl, for_, intercalate, traverse_)
import Data.Lens (_Just, assign, has, modifying, over, preview, previewOn, to, toArrayOf, traversed, use, (^.), (^?))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.List.NonEmpty as NEL
import Data.Map (Map)
import Data.Map as Map
import Data.Map.Lens (_MaxIndex, _NextIndex)
import Data.Maybe (Maybe(..), fromMaybe, isNothing, maybe)
import Data.Newtype (unwrap)
import Data.NonEmptyList.Extra (extendWith)
import Data.NonEmptyList.Lens (_Tail)
import Data.Set as Set
import Data.String (Pattern(..), split)
import Data.Traversable (for)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (ClassName(..), Component, HalogenM, raise)
import Halogen as H
import Halogen.Analytics (withAnalytics)
import Halogen.Classes (aHorizontal, active, bold, closeDrawerIcon, expanded, first, fullHeight, infoIcon, jFlexStart, minusBtn, noMargins, plusBtn, pointer, rTable, rTable4cols, rTableCell, rTableDataRow, rTableEmptyRow, sidebarComposer, smallBtn, spaceLeft, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (HTML, a, article, aside, b_, br_, button, div, h6, hr_, img, input, li, option, p, p_, section, select, small, small_, strong_, text, ul)
import Halogen.HTML (code_, span) as HTML
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, selected, src, type_, value)
import Halogen.HTML.Properties (value) as HTML
import Help (HelpContext(..), toHTML)
import Marlowe.Extended (toCore)
import Marlowe.Extended as EM
import Marlowe.Holes (fromTerm, gatherContractData)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId, Assets(..), Bound(..), ChoiceId(..), Contract(..), Input(..), Party, Payment(..), PubKey, Token(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, inBounds, timeouts)
import Marlowe.Semantics as S
import Pretty (renderPrettyParty, renderPrettyPayee, renderPrettyToken, showPrettyMoney)
import SimulationPage.Types (ActionInput(..), ActionInputId, MarloweState, _SimulationRunning, _contract, _currentContract, _executionState, _marloweState, _payments, _pendingInputs, _possibleActions, _slot, _state, _transactionError, _transactionWarnings, emptyMarloweStateWithSlot, mapPartiesActionInput)
import Simulator (updateContractInStateP, updatePossibleActions, updateStateP)
import Text.Extra (stripParens)
import Text.Pretty (pretty)
import WalletSimulation.Types (Action(..), ChildSlots, LoadedContract, Message(..), Query(..), State, View(..), Wallet(..), _addInputError, _assetChanges, _assets, _contracts, _currentLoadedMarloweState, _helpContext, _initialized, _loadContractError, _loadedMarloweState, _name, _openWallet, _parties, _runningContracts, _showRightPanel, _started, _tokens, _view, _walletContracts, _walletLoadedContract, _wallets, mkState)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

mkComponent :: forall m. MonadEffect m => Component HTML Query Unit Message m
mkComponent =
  H.mkComponent
    { initialState: const mkState
    , render
    , eval:
        H.mkEval
          { handleAction: withAnalytics handleAction
          , handleQuery
          , initialize: Just Init
          , receive: const Nothing
          , finalize: Nothing
          }
    }

applyTransactions :: forall m. MonadState State m => m Unit
applyTransactions = do
  initialPayments <- fromMaybe mempty <$> peruse (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _payments)
  modifying _loadedMarloweState (extendWith (updatePossibleActions <<< updateStateP))
  updatedPayments <- fromMaybe mempty <$> peruse (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _payments)
  let
    newPayments = drop (Array.length initialPayments) updatedPayments
  mContract <- use _walletLoadedContract
  case mContract of
    Nothing -> pure unit -- shouldn't be possible really
    Just contract -> traverse_ (makePayment contract) newPayments
  where
  makePayment contract (Payment party money) = do
    let
      owner = fromMaybe mempty (contract ^? (_parties <<< ix party))

      (assets :: Array _) = Map.toUnfoldable $ joinMaps (unwrap money)
    for assets \(Tuple (Tuple currencySymbol tokenName) amount) -> do
      let
        token = Token currencySymbol tokenName

        addMoney Nothing = Just amount

        addMoney (Just v) = Just (v + amount)
      modifying (_wallets <<< ix owner <<< _assets) (Map.alter addMoney token)

hasHistory :: State -> Boolean
hasHistory = has (_loadedMarloweState <<< _Tail)

handleQuery :: forall a m. Query a -> HalogenM State Action ChildSlots Message m (Maybe a)
handleQuery (LoadContract contractString next) = do
  case parseContract contractString of
    Left err -> assign _loadContractError (Just $ show err)
    Right contractTerm ->
      for_ (fromTerm contractTerm) \extendedContract -> do
        -- We reuse the extended Marlowe parser for now since it is a superset
        for_ (toCore (extendedContract :: EM.Contract)) \contract -> do
          idx <- use (_contracts <<< _NextIndex)
          mOpenWallet <- use _openWallet
          for_ mOpenWallet \openWallet -> do
            existingWallets <- use _wallets
            slot <- use _slot
            let
              contractData = gatherContractData contractTerm { parties: mempty, tokens: mempty }

              parties = Set.mapMaybe fromTerm contractData.parties

              tokens = Map.fromFoldable $ Set.map (\token -> Tuple token zero) $ Set.mapMaybe fromTerm contractData.tokens

              newWallets = foldl (walletFromPK tokens) existingWallets parties

              -- A PK party should be owned by the wallet that is that PK but by default it is owned by the primary wallet
              partiesMap = Map.fromFoldable $ Set.map (mkPartyPair openWallet newWallets) parties

              loadedContract =
                { contract
                , idx
                , owner: openWallet ^. _name
                , parties: mempty
                , started: false
                , marloweState: NEL.singleton (emptyMarloweStateWithSlot slot contract)
                }
            modifying _wallets (Map.union newWallets)
            assign _walletLoadedContract (Just loadedContract)
            modifying _contracts (Map.insert idx loadedContract)
            assign (_walletLoadedContract <<< _Just <<< _parties) partiesMap
            modifying (_openWallet <<< _Just <<< _assets) (flip Map.union tokens)
            modifying _tokens (Set.union (Map.keys tokens))
            updateContractInState contractString
  pure $ Just next
  where
  walletFromPK :: Map Token BigInteger -> Map String Wallet -> Party -> Map String Wallet
  walletFromPK assets wallets (S.PK pubKey) =
    if Map.member pubKey wallets then
      wallets
    else
      Map.insert pubKey (Wallet { name: pubKey, assets, loadedContract: Nothing }) wallets

  walletFromPK _ wallets _ = wallets

  mkPartyPair :: Wallet -> Map String Wallet -> Party -> Tuple Party String
  mkPartyPair defaultOwner wallets (S.PK pubKey) =
    foldl
      (\(Tuple party owner) (Wallet { name }) -> if pubKey == name then Tuple party name else Tuple party owner)
      (Tuple (S.PK pubKey) (defaultOwner ^. _name))
      wallets

  mkPartyPair defaultOwner _ party = Tuple party (defaultOwner ^. _name)

updateMarloweState :: forall m. MonadState State m => (MarloweState -> MarloweState) -> m Unit
updateMarloweState f = modifying _loadedMarloweState (extendWith (updatePossibleActions <<< f))

updateContractInState :: forall m. MonadState State m => String -> m Unit
updateContractInState contents = modifying _currentLoadedMarloweState (updatePossibleActions <<< updateContractInStateP contents)

handleAction ::
  forall m.
  MonadEffect m =>
  Action -> HalogenM State Action ChildSlots Message m Unit
handleAction Init = pure unit

handleAction (ShowRightPanel val) = assign _showRightPanel val

handleAction LoadContractFromSimulation = raise SendContractToWallet

handleAction StartContract = do
  mContract <- use _walletLoadedContract
  case mContract of
    Just contract -> do
      assign _initialized true
      assign (_walletLoadedContract <<< _Just <<< _started) true
      updateContractInState (stripParens $ show $ pretty $ contract.contract)
    Nothing -> assign _loadContractError $ Just "Can't start since no contract has been loaded"

handleAction ResetContract = do
  mContract <- use _walletLoadedContract
  assign _slot zero
  assign (_contracts <<< traversed <<< _started) false
  assign (_contracts <<< traversed <<< _marloweState) (NEL.singleton (emptyMarloweStateWithSlot zero (maybe Close (\x -> x.contract) mContract)))

handleAction ResetAll = do
  assign _initialized false
  assign _walletLoadedContract Nothing
  assign _wallets mempty
  assign _contracts mempty
  assign _openWallet Nothing
  assign _view Home

handleAction NextSlot = do
  modifying _slot (add one)
  modifying (_contracts <<< traversed <<< _marloweState)
    (extendWith (updatePossibleActions <<< over (_executionState <<< _SimulationRunning <<< _slot) (add one)))

handleAction ApplyTransaction = do
  assign _addInputError Nothing
  applyTransactions

handleAction (ChangeRoleOwner contractId party newName) = do
  assign (_contracts <<< ix contractId <<< _parties <<< ix party) newName
  pubKey <- fromMaybe mempty <$> peruse (_openWallet <<< _Just <<< _name)
  contracts <- use (_walletContracts pubKey <<< to Map.values <<< to Array.fromFoldable)
  when (Array.null contracts) $ assign _walletLoadedContract Nothing

handleAction (SelectWallet wallet) = do
  mContract <- use _walletLoadedContract
  walletContracts <- use (_walletContracts (wallet ^. _name))
  assign _openWallet (Just wallet)
  case mContract of
    Just contract ->
      if (Map.member contract.idx walletContracts) then do
        assign _walletLoadedContract (Just contract)
        assign _addInputError Nothing
      else
        assign _walletLoadedContract Nothing
    _ -> pure unit
  assign _view $ WalletView $ wallet ^. _name

handleAction (AddInput input@(IDeposit _ _ token amount) bounds) = do
  assign _addInputError Nothing
  mWalletAmount <- peruse (_openWallet <<< _Just <<< _assets <<< ix token)
  case mWalletAmount of
    Nothing -> pure unit
    Just walletAmount ->
      if walletAmount >= amount then do
        assign (_openWallet <<< _Just <<< _assets <<< ix token) (walletAmount - amount)
        updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) ((flip snoc) input))
      else
        assign _addInputError $ Just "Insufficient funds to add this input"

handleAction (AddInput input bounds) = do
  assign _addInputError Nothing
  let
    validChoice = case input of
      (IChoice _ chosenNum) -> inBounds chosenNum bounds
      _ -> true
  if validChoice then
    updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) ((flip snoc) input))
  else
    assign _addInputError $ Just "Invalid Choice"

handleAction (RemoveInput input@(IDeposit _ _ token amount)) = do
  assign _addInputError Nothing
  modifying (_openWallet <<< _Just <<< _assets <<< ix token) (\v -> v + amount)
  updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) (delete input))

handleAction (RemoveInput input) = do
  assign _addInputError Nothing
  updateMarloweState (over (_executionState <<< _SimulationRunning <<< _pendingInputs) (delete input))

handleAction (SetChoice choiceId chosenNum) = updateMarloweState (over (_executionState <<< _SimulationRunning <<< _possibleActions) (mapPartiesActionInput (updateChoice choiceId)))
  where
  updateChoice :: ChoiceId -> ActionInput -> ActionInput
  updateChoice wantedChoiceId input@(ChoiceInput currentChoiceId bounds _)
    | wantedChoiceId == currentChoiceId = ChoiceInput choiceId bounds chosenNum

  updateChoice _ input = input

handleAction (ChangeCurrencyInput token money) = modifying _assetChanges (Map.insert token money)

handleAction (AddCurrency token) = do
  money <- peruse (_assetChanges <<< ix token)
  modifying (_openWallet <<< _Just <<< _assets) (Map.alter (addMoney money) token)
  where
  addMoney (Just newMoney) (Just oldMoney)
    | newMoney > zero = Just $ oldMoney + newMoney

  addMoney _ oldValue = oldValue

handleAction (RenameWallet name) = assign (_openWallet <<< _Just <<< _name) name

handleAction CreateWallet = do
  idx <- use (_wallets <<< _NextIndex)
  let
    name = "Wallet " <> show idx

    wallet = Wallet { name, assets: Map.singleton (Token "" "") zero, loadedContract: Nothing }
  modifying _wallets (Map.insert name wallet)
  assign _openWallet (Just wallet)
  assign _view $ WalletView $ wallet ^. _name

handleAction (SelectContract contract) = do
  assign _walletLoadedContract (Just contract)
  assign _addInputError Nothing

handleAction (ChangeHelpContext help) = do
  assign _helpContext help
  scrollHelpPanel

scrollHelpPanel :: forall m. MonadEffect m => HalogenM State Action ChildSlots Message m Unit
scrollHelpPanel =
  liftEffect do
    window <- Web.window
    document <- toDocument <$> W.document window
    mSidePanel <- WC.item 0 =<< D.getElementsByClassName "sidebar-composer" document
    case mSidePanel of
      Nothing -> pure unit
      Just sidePanel -> do
        scrollHeight <- E.scrollHeight sidePanel
        setScrollTop scrollHeight sidePanel

render :: forall p. State -> HTML p Action
render state =
  div [ classes [ ClassName "full-height" ] ]
    [ section [ classes [ aHorizontal ] ]
        [ div [ classes [ aHorizontal ] ]
            [ div [ classes [ ClassName "wallet-title", aHorizontal, jFlexStart ] ]
                [ div [ classes [ ClassName "demos", spaceLeft ] ]
                    [ small_ [ text "Created Wallets:" ]
                    ]
                ]
            , ul [ classes [ ClassName "wallet-list", aHorizontal ] ]
                (map (displayWallet walletName) wallets)
            , addWalletButton
            , a [ class_ (ClassName "clear-all-contracts"), onClick $ const $ Just ResetAll ] [ text "Clear All" ]
            ]
        , div [ classes [ expanded (state ^. _showRightPanel) ] ]
            [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (state ^. (_showRightPanel <<< to not)) ]
                [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
            ]
        ]
    , section [ classes [ fullHeight ] ]
        [ mainPanel state
        , rightPanel state
        ]
    ]
  where
  walletName = fromMaybe "No Wallet Open" $ state ^? (_openWallet <<< _Just <<< _name)

  wallets = toArrayOf (_wallets <<< traversed) state

  addWalletButton = button [ class_ (ClassName "add-wallet-button"), onClick $ const $ Just CreateWallet ] [ text "+" ]

displayWallet :: forall p. PubKey -> Wallet -> HTML p Action
displayWallet openWallet wallet =
  li
    [ classes
        ( if wallet ^. _name == openWallet then
            [ active ]
          else
            mempty
        )
    ]
    [ a [ onClick $ const $ Just $ SelectWallet wallet ] [ text $ show wallet ]
    ]

mainPanel ::
  forall p.
  State ->
  HTML p Action
mainPanel state =
  div [ class_ (ClassName "wallet-contents") ] case state ^. _view of
    Home -> []
    WalletView walletName ->
      ( [ div [ class_ (ClassName "wallet-top-section") ]
            [ renderAssets state
            , renderMyRoles walletName state
            ]
        , hr_
        , renderContracts state
        , hr_
        ]
          <> renderContract'
      )
  where
  started = fromMaybe false $ preview (_walletLoadedContract <<< _Just <<< _started) state

  loaded = has _walletLoadedContract state

  renderContract'
    | not loaded = []

  renderContract'
    | not started =
      [ button
          [ classes [ ClassName "tooltip" ]
          , onClick $ const $ Just $ StartContract
          ]
          [ text "Start"
          ]
      , div [ classes [ ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (HTML.code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") contractString

  renderContract'
    | otherwise =
      [ div [ class_ (ClassName "wallet-composer") ]
          ( renderActions state
              <> [ renderCurrentState state
                ]
          )
      , div [ classes [ ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (HTML.code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") contractString

  contractString =
    fromMaybe mempty do
      contract <-
        preview (_walletLoadedContract <<< _Just <<< _currentContract) state
          <|> preview (_walletLoadedContract <<< _Just <<< _contract) state
      pure $ show $ pretty contract

renderActions :: forall p. State -> Array (HTML p Action)
renderActions state =
  [ div [ class_ (ClassName "wallet-composer-actions") ]
      ( [ div [ class_ aHorizontal ]
            [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
                [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Input Composer" ] ]
            , a [ onClick $ const $ Just $ ChangeHelpContext InputComposerHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
            ]
        ]
          <> [ div [ class_ (ClassName "composer") ]
                ( if Array.null possibleActions then
                    [ text "no possible actions" ]
                  else
                    [ ul [ class_ (ClassName "wallet-actions") ] (map renderAction possibleActions)
                    , HTML.span [ class_ (ClassName "choice-error") ] [ text (state ^. (_addInputError <<< to (fromMaybe mempty))) ]
                    ]
                )
            ]
          <> [ div [ classes [ aHorizontal ] ]
                [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
                    [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Transaction Composer" ] ]
                , a [ onClick $ const $ Just $ ChangeHelpContext TransactionComposerHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
                ]
            ]
          <> [ div [ classes [ ClassName "composer" ] ]
                ( if hasTransactions then
                    [ transactionComposer state
                    , div [ class_ (ClassName "transaction-btns") ]
                        [ ul [ classes [ aHorizontal ] ]
                            [ li [ class_ (ClassName "apply-transaction-button") ]
                                [ button
                                    [ onClick $ const $ Just ApplyTransaction
                                    , enabled hasTransactions
                                    , class_ (Classes.disabled $ not hasTransactions)
                                    ]
                                    [ text "Apply" ]
                                ]
                            ]
                        ]
                    ]
                  else
                    [ text "no transactions" ]
                )
            ]
      )
  ]
  where
  pendingInputs = fromMaybe mempty (state ^? (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _pendingInputs))

  possibleActions =
    fromMaybe mempty
      $ state
      ^? ( _currentLoadedMarloweState
            <<< _executionState
            <<< _SimulationRunning
            <<< _possibleActions
            <<< to unwrap
            <<< to (Map.filterKeys walletKeys)
            <<< to Map.values
            <<< to (map Map.toUnfoldable)
            <<< to fold
        )

  walletKeys party =
    let
      parties = fromMaybe mempty $ state ^? (_walletLoadedContract <<< _Just <<< _parties)

      walletParties = case state ^? (_openWallet <<< _Just) of
        Just wallet -> Set.fromFoldable $ Map.keys $ Map.filter (eq (wallet ^. _name)) parties
        Nothing -> mempty
    in
      Set.member party walletParties

  hasTransactions = has (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _pendingInputs <<< to Array.null <<< to not) state

  renderAction :: (Tuple ActionInputId ActionInput) -> HTML p Action
  renderAction (Tuple actionInputId actionInput) = inputItem true "" actionInput

renderMyRoles :: forall p. PubKey -> State -> HTML p Action
renderMyRoles me state =
  div [ classes [ ClassName "centre-element" ] ]
    [ h6 [ classes [ ClassName "parties-heading", noMargins ] ]
        [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "My Roles" ] ]
    , Keyed.ul [] (map (displayMyRole me wallets) myRoles)
    ]
  where
  wallets = map snd $ Map.toUnfoldable $ state ^. _wallets

  myRoles =
    Array.fromFoldable
      $ Set.mapMaybe
          ( \(Tuple contract party) -> do
              name <- getRoleName party
              pure (Tuple contract name)
          )
      $ Map.keys
      $ Map.filter (eq me)
      $ joinMaps
      $ map (_.parties)
      $ state.contracts

  getRoleName (S.Role name) = Just name

  getRoleName _ = Nothing

joinMaps :: forall a b c. Ord a => Ord b => Map a (Map b c) -> Map (Tuple a b) c
joinMaps container =
  let
    (containerArr :: Array _) = Map.toUnfoldable container
  in
    Map.fromFoldable
      $ Array.foldl
          ( \acc (Tuple a m) ->
              let (arr :: Array _) = Map.toUnfoldable m in acc <> (map (\(Tuple b c) -> Tuple (Tuple a b) c) arr)
          )
          mempty
          containerArr

displayMyRole :: forall p. PubKey -> Array Wallet -> Tuple Int String -> Tuple String (HTML p Action)
displayMyRole myWalletId wallets (Tuple contractId roleName) =
  Tuple ("Contract " <> show contractId <> " - " <> roleName)
    ( li []
        [ p [ class_ bold ] [ text $ "Contract " <> show contractId <> " - " <> roleName ]
        , div [ classes [ ClassName "a-horizontal", ClassName "roles" ] ]
            [ p_ [ text ("transfer ownership to ") ]
            , select
                [ class_ (ClassName "dropdown-header")
                , onValueChange (\idx -> Just $ ChangeRoleOwner contractId (S.Role roleName) idx)
                ]
                (map item wallets)
            ]
        ]
    )
  where
  item wallet
    | (wallet ^. _name) == myWalletId = option [ selected true, class_ (ClassName "selected-item"), HTML.value myWalletId ] [ text myWalletId ]
    | otherwise = option [ selected false, HTML.value (show wallet) ] [ text $ show wallet ]

displayParty :: forall p. Map String Wallet -> Tuple Party String -> HTML p Action
displayParty wallets (Tuple party owner) = case Map.lookup owner wallets, party of
  (Just _), (S.PK _) -> li [] [ text $ showParty party ]
  (Just wallet), _ ->
    li []
      [ text (showParty party <> " owned by " <> (wallet ^. _name))
      ]
  _, _ ->
    li []
      [ text (showParty party <> " with unknown owner")
      ]
  where
  showParty (S.PK v) = "Public Key \"" <> v <> "\""

  showParty (S.Role v) = "Role \"" <> v <> "\""

renderCurrentState :: forall p action. State -> HTML p action
renderCurrentState state =
  div [ classes [ active, ClassName "wallet-composer-state" ] ]
    [ div [ classes [ rTable, rTable4cols ] ]
        ( warningsRow <> errorRow
            <> dataRow "Expiration Slot" (contractMaxTime (previewOn state (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _contract)))
            <> tableRow
                { title: "Accounts"
                , emptyMessage: "No accounts have been used"
                , columns: ("Participant" /\ "Assets" /\ mempty)
                , rowData: accountsData
                }
            <> tableRow
                { title: "Choices"
                , emptyMessage: "No Choices have been made"
                , columns: ("ID" /\ "Participant" /\ "Value")
                , rowData: choicesData
                }
            <> tableRow
                { title: "Payments"
                , emptyMessage: "No payments have been recorded"
                , columns: ("Party" /\ "Asset" /\ mempty)
                , rowData: paymentsData
                }
            <> tableRow
                { title: "Let Bindings"
                , emptyMessage: "No values have been bound"
                , columns: ("Identifier" /\ "Value" /\ mempty)
                , rowData: bindingsData
                }
        )
    ]
  where
  contractMaxTime Nothing = "Closed"

  contractMaxTime (Just contract) =
    let
      t = (_.maxTime <<< unwrap <<< timeouts) contract
    in
      if t == zero then "Closed" else show t

  warnings = state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _transactionWarnings)

  warningsRow =
    if Array.null warnings then
      []
    else
      (headerRow "Warnings" ("type" /\ "details" /\ mempty)) <> foldMap displayWarning' warnings

  errorRow = case state ^? (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _transactionError) of
    Nothing -> []
    Just error ->
      if isNothing error then
        []
      else
        (headerRow "Errors" ("details" /\ mempty /\ mempty)) <> displayError error

  displayError Nothing = []

  displayError (Just err) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ classes [ rTableCell, ClassName "Rtable-single-column-row" ] ] [ text $ show err ]
    ]

  accountsData =
    let
      (accounts :: Array _) = state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple accountOwner token) value) = stripParens (show accountOwner) /\ (show value <> " " <> shortTokenString token) /\ mempty
    in
      map asTuple accounts

  shortTokenString (Token "" "") = "Ada"

  shortTokenString (Token currSym tokName) = currSym <> " " <> tokName

  choicesData =
    let
      (choices :: Array _) = state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = show choiceName /\ stripParens (show choiceOwner) /\ show value
    in
      map asTuple choices

  paymentsData =
    let
      payments = state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _payments)

      asTuple :: Payment -> Array (String /\ String /\ String)
      asTuple (Payment party (Assets mon)) =
        concatMap
          ( \(Tuple currencySymbol tokenMap) ->
              ( map
                  ( \(Tuple tokenName value) ->
                      stripParens (show party) /\ (show value <> " " <> shortTokenString (Token currencySymbol tokenName)) /\ mempty
                  )
                  (Map.toUnfoldable tokenMap)
              )
          )
          (Map.toUnfoldable mon)
    in
      concatMap asTuple payments

  bindingsData =
    let
      (bindings :: Array _) = state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _state <<< _boundValues <<< to Map.toUnfoldable)

      asTuple (Tuple (ValueId valueId) value) = show valueId /\ show value /\ mempty
    in
      map asTuple bindings

  tableRow { title, emptyMessage, rowData: [] } = emptyRow title emptyMessage

  tableRow { title, columns, rowData } = headerRow title columns <> foldMap (\dataTuple -> row dataTuple) rowData

  headerRow title (a /\ b /\ c) =
    [ div [ classes [ rTableCell, first, Classes.header ] ] [ text title ] ]
      <> map (\x -> div [ classes [ rTableCell, rTableCell, Classes.header ] ] [ text x ]) [ a, b, c ]

  row (a /\ b /\ c) =
    [ div [ classes [ rTableCell, first ] ] [] ]
      <> map (\x -> div [ class_ rTableCell ] [ text x ]) [ a, b, c ]

  emptyRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableEmptyRow, Classes.header ] ] [ text message ]
    ]

  dataRow title message =
    [ div [ classes [ rTableCell, first, Classes.header ] ]
        [ text title ]
    , div [ classes [ rTableCell, rTableDataRow ] ] [ text message ]
    ]

  displayWarning' (TransactionNonPositiveDeposit party owner tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositiveDeposit" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "Party "
        , renderPrettyParty party
        , text $ " is asked to deposit "
            <> showPrettyMoney amount
            <> " units of "
        , renderPrettyToken tok
        , text " into account of "
        , renderPrettyParty owner
        , text "."
        ]
    ]

  displayWarning' (TransactionNonPositivePay owner payee tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositivePay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        ( [ text $ "The contract is supposed to make a payment of "
              <> showPrettyMoney amount
              <> " units of "
          , renderPrettyToken tok
          , text $ " from account of "
              <> show owner
              <> " to "
          ]
            <> renderPrettyPayee payee
            <> [ text "." ]
        )
    ]

  displayWarning' (TransactionPartialPay owner payee tok amount expected) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionPartialPay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        ( [ text $ "The contract is supposed to make a payment of "
              <> showPrettyMoney expected
              <> " units of "
          , renderPrettyToken tok
          , text " from account of "
          , renderPrettyParty owner
          , text $ " to "
          ]
            <> renderPrettyPayee payee
            <> [ text $ "."
                  <> " but there is only "
                  <> showPrettyMoney amount
                  <> "."
              ]
        )
    ]

  displayWarning' (TransactionShadowing valId oldVal newVal) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionShadowing" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract defined the value with id "
            <> show valId
            <> " before, it was assigned the value "
            <> show oldVal
            <> " and now it is being assigned the value "
            <> show newVal
            <> "."
        ]
    ]

  displayWarning' TransactionAssertionFailed =
    [ b_ [ text "TransactionAssertionFailed" ]
    , text " - An assertion in the contract did not hold."
    ]

renderAssets :: forall p. State -> HTML p Action
renderAssets state =
  div []
    ( [ h6 [ class_ noMargins ]
          [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Assets" ]
          ]
      ]
        <> map currencyRow allTokens
    )
  where
  emptyTokens = Map.fromFoldable $ Set.map (\t -> Tuple t zero) $ state ^. _tokens

  walletTokens = state ^. (_openWallet <<< _Just <<< _assets)

  allTokens = Map.toUnfoldable $ Map.union walletTokens emptyTokens

  currencyRow :: Tuple Token BigInteger -> HTML p Action
  currencyRow (Tuple token@(Token currencySymbol tokenName) money) =
    div [ class_ (ClassName "currency-row") ]
      ( [ div []
            ( case currencySymbol, tokenName of
                "", "" -> [ b_ [ text $ show money <> " Ada" ] ]
                _, _ ->
                  [ b_ [ text $ show money ]
                  , spanText " "
                  , b_ [ text currencySymbol ]
                  , spanText " "
                  , b_ [ text tokenName ]
                  ]
            )
        ]
          <> [ div []
                [ addCurrencyInput
                , addCurrencyButton
                ]
            ]
      )
    where
    addCurrencyInput =
      input
        [ type_ InputNumber
        , placeholder "BigInteger"
        , class_ $ ClassName "currency-input"
        , value "0"
        , onValueChange (\newMoney -> ChangeCurrencyInput token <$> BigInteger.fromString newMoney)
        ]

    addCurrencyButton = button [ onClick $ const $ Just $ AddCurrency token ] [ text "+" ]

renderContracts :: forall p. State -> HTML p Action
renderContracts state =
  let
    pubKey = fromMaybe mempty (state ^? (_openWallet <<< _Just <<< _name))

    contracts = state ^. (_walletContracts pubKey <<< to Map.values <<< to Array.fromFoldable)
  in
    div [ classes [ aHorizontal ] ]
      [ div [ classes [ ClassName "wallet-title", aHorizontal, jFlexStart ] ]
          [ div [ classes [ ClassName "demos", spaceLeft ] ]
              [ small_ [ text "Contracts:" ]
              ]
          ]
      , ul [ classes [ ClassName "wallet-list", aHorizontal ] ]
          ( ( if Array.null contracts then
                [ li [ class_ (ClassName "contract-link") ] [ text "No contracts currently loaded" ] ]
              else
                map (renderContract state) contracts
            )
              <> [ button
                    [ class_ (ClassName "load-contract-from-simulator-button")
                    , onClick $ const $ Just LoadContractFromSimulation
                    ]
                    [ text "Load Contract from Simulation" ]
                ]
          )
      ]
  where
  involvesWallet contract = true

renderContract :: forall p. State -> LoadedContract -> HTML p Action
renderContract state contract =
  li
    [ ( classes
          ( [ ClassName "contract-link" ]
              <> if (state ^? (_walletLoadedContract <<< _Just <<< to _.idx)) == Just contract.idx then
                  [ active ]
                else
                  [ ClassName mempty ]
          )
      )
    ]
    [ a [ onClick $ const $ Just $ SelectContract contract ] [ text $ "Contract " <> (show contract.idx) ]
    ]

inputItem ::
  forall p.
  Boolean ->
  PubKey ->
  ActionInput ->
  HTML p Action
inputItem isEnabled person (DepositInput accountId party token value) =
  li [ classes [ aHorizontal ] ]
    [ p_ (renderDeposit accountId party token value)
    , button
        [ classes [ plusBtn, smallBtn, (Classes.disabled $ not isEnabled) ]
        , enabled isEnabled
        , onClick $ const $ Just
            $ AddInput (IDeposit accountId party token value) []
        ]
        [ text "+" ]
    ]

inputItem isEnabled person (ChoiceInput choiceId@(ChoiceId choiceName choiceOwner) bounds chosenNum) =
  li
    [ classes [ aHorizontal, ClassName "choice-row" ] ]
    ( [ div []
          [ p [ class_ (ClassName "choice-input") ]
              [ b_ [ spanText (show choiceOwner) ]
              , spanText " make choice "
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
          [ classes [ plusBtn, smallBtn ]
          , onClick $ const $ Just
              $ AddInput (IChoice (ChoiceId choiceName choiceOwner) chosenNum) bounds
          ]
          [ text "+" ]
      ]
    else
      []

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
            $ AddInput INotify []
        ]
        [ text "+" ]
    ]

inputItem _ _ _ = text mempty

marloweActionInput :: forall p a action. Show a => Boolean -> (BigInteger -> action) -> a -> HTML p action
marloweActionInput isEnabled f current =
  input
    [ type_ InputNumber
    , enabled isEnabled
    , placeholder "BigInteger"
    , class_ $ ClassName "action-input"
    , value $ show current
    , onValueChange (map f <<< BigInteger.fromString)
    ]

renderDeposit :: forall p a. AccountId -> S.Party -> Token -> BigInteger -> Array (HTML p a)
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

transactionComposer ::
  forall p.
  State ->
  HTML p Action
transactionComposer state =
  ul [ class_ (ClassName "participants") ]
    if Array.null pendingInputs then
      [ text "Empty transaction" ]
    else
      [ transaction state ]
  where
  currentBlock = state ^? (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _slot)

  pendingInputs = fromMaybe mempty (state ^? (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _pendingInputs))

transaction ::
  forall p.
  State ->
  HTML p Action
transaction state =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    [ ul
        []
        (map (transactionRow state) (state ^. (_currentLoadedMarloweState <<< _executionState <<< _SimulationRunning <<< _pendingInputs)))
    ]

transactionRow ::
  forall p.
  State ->
  Input ->
  HTML p Action
transactionRow state input@(IDeposit accountOwner party token money) =
  li [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_
        [ text "Deposit "
        , strong_ [ text (show money) ]
        , text " units of "
        , strong_ [ text (show token) ]
        , text " into account "
        , strong_ [ text (show accountOwner) ]
        , text " as "
        , strong_ [ text (show party) ]
        ]
    , button
        [ classes [ minusBtn, smallBtn, bold ]
        , onClick $ const $ Just $ RemoveInput input
        ]
        [ text "-" ]
    ]

transactionRow state input@(IChoice (ChoiceId choiceName choiceOwner) chosenNum) =
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
        [ classes [ minusBtn, smallBtn, bold ]
        , onClick $ const $ Just $ RemoveInput input
        ]
        [ text "-" ]
    ]

transactionRow state INotify =
  li [ classes [ ClassName "choice-a", aHorizontal ] ]
    [ p_
        [ text "Notification"
        ]
    , button
        [ classes [ minusBtn, smallBtn, bold ]
        , onClick $ const $ Just $ RemoveInput INotify
        ]
        [ text "-" ]
    ]

rightPanel ::
  forall p.
  State ->
  HTML p Action
rightPanel state =
  aside [ classes [ sidebarComposer, expanded showRightPanel ] ]
    [ div [ class_ aHorizontal ]
        [ h6 [ classes [ ClassName "global-actions-heading", noMargins ] ]
            [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Blockchain Status" ] ]
        ]
    , ul []
        [ li [] [ text ((state ^. (_runningContracts <<< _MaxIndex <<< to show)) <> " contracts running") ]
        , li [] [ text $ "Current Slot: " <> show currentBlock ]
        , li [ classes [ bold, pointer ] ]
            [ a
                [ onClick $ const $ Just ResetContract
                ]
                [ text "Reset Blockchain" ]
            ]
        , li [ classes [ bold, pointer ] ]
            [ a
                [ onClick $ const $ Just NextSlot
                ]
                [ text $ "Next Slot" ]
            ]
        ]
    , article [ class_ (ClassName "documentation-panel") ]
        (toHTML (state ^. _helpContext))
    ]
  where
  showRightPanel = state ^. _showRightPanel

  currentBlock = state ^. _slot
