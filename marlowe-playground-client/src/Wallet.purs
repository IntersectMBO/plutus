module Wallet where

import Analytics (class IsEvent, Event)
import Analytics as A
import Control.Alt ((<|>))
import Control.Monad.State (class MonadState)
import Data.Array (concatMap, delete, drop, elem, find, fold, foldMap, snoc)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Foldable (foldl, for_, intercalate, traverse_)
import Data.Lens (Getter', Lens', _Just, assign, has, lens, modifying, over, preview, set, to, toArrayOf, traversed, use, (^.), (^?))
import Data.Lens.Extra (peruse)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List.NonEmpty as NEL
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Map.Lens (_MaxIndex, _NextIndex)
import Data.Maybe (Maybe(..), fromMaybe, isNothing)
import Data.Newtype (class Newtype, unwrap)
import Data.NonEmptyList.Extra (extendWith)
import Data.NonEmptyList.Lens (_Tail)
import Data.Profunctor.Choice (class Choice)
import Data.Profunctor.Strong (class Strong)
import Data.Set (Set)
import Data.Set as Set
import Data.String (Pattern(..), split)
import Data.Symbol (SProxy(..))
import Data.Traversable (for)
import Data.Tuple (Tuple(..), snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (ClassName(..), Component, HalogenM, raise)
import Halogen as H
import Halogen.Analytics (handleActionWithAnalyticsTracking)
import Halogen.Classes (aHorizontal, active, bold, closeDrawerIcon, expanded, first, infoIcon, jFlexStart, minusBtn, noMargins, panelSubHeader, panelSubHeaderMain, panelSubHeaderSide, plusBtn, pointer, rTable, rTable4cols, rTableCell, rTableDataRow, rTableEmptyRow, sidebarComposer, smallBtn, spaceLeft, spanText, textSecondaryColor, uppercase)
import Halogen.Classes as Classes
import Halogen.HTML (HTML, a, article, aside, b_, br_, button, div, h6, hr_, img, input, li, option, p, p_, section, select, small, small_, strong_, text, ul)
import Halogen.HTML (code_, span) as HTML
import Halogen.HTML.Elements.Keyed as Keyed
import Halogen.HTML.Events (onClick, onValueChange)
import Halogen.HTML.Properties (InputType(..), alt, class_, classes, enabled, placeholder, selected, src, type_, value)
import Halogen.HTML.Properties (value) as HTML
import Help (HelpContext(..), toHTML)
import Marlowe.Holes (fromTerm, gatherContractData)
import Marlowe.Parser (parseContract)
import Marlowe.Semantics (AccountId(..), Assets(..), Bound(..), ChoiceId(..), ChosenNum, Input(..), Party, Payee(..), Payment(..), PubKey, Slot, Token(..), TransactionWarning(..), ValueId(..), _accounts, _boundValues, _choices, inBounds, timeouts)
import Marlowe.Semantics as S
import Prelude (class Eq, class Ord, class Show, Unit, add, bind, const, discard, eq, flip, map, mempty, not, one, otherwise, pure, show, unit, when, zero, ($), (&&), (+), (-), (<$>), (<<<), (<>), (=<<), (==), (>=), (||), (>))
import Simulation.State (ActionInput(..), ActionInputId, MarloweState, _contract, _currentMarloweState, _marloweState, _payments, _pendingInputs, _possibleActions, _slot, _state, _transactionError, _transactionWarnings, emptyMarloweState, mapPartiesActionInput, updateContractInStateP, updatePossibleActions, updateStateP)
import Text.Extra (stripParens)
import Text.Pretty (pretty)
import Web.DOM.Document as D
import Web.DOM.Element (setScrollTop)
import Web.DOM.Element as E
import Web.DOM.HTMLCollection as WC
import Web.HTML as Web
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.Window as W

newtype Wallet
  = Wallet
  { name :: PubKey
  , assets :: Map Token BigInteger
  , loadedContract :: Maybe Int
  }

derive instance newtypeWallet :: Newtype Wallet _

derive instance eqWallet :: Eq Wallet

derive instance ordWallet :: Ord Wallet

instance showWallet :: Show Wallet where
  show (Wallet { name }) = name

_assets :: Lens' Wallet (Map Token BigInteger)
_assets = _Newtype <<< prop (SProxy :: SProxy "assets")

_name :: Lens' Wallet PubKey
_name = _Newtype <<< prop (SProxy :: SProxy "name")

_loadedContract :: Lens' Wallet (Maybe Int)
_loadedContract = _Newtype <<< prop (SProxy :: SProxy "loadedContract")

type LoadedContract
  = { idx :: Int
    , owner :: PubKey
    , contract :: S.Contract
    , parties :: Map Party PubKey
    , started :: Boolean
    , marloweState :: NonEmptyList MarloweState
    }

_parties :: Lens' LoadedContract (Map Party PubKey)
_parties = prop (SProxy :: SProxy "parties")

isInvolvedInContract :: PubKey -> LoadedContract -> Boolean
isInvolvedInContract pubKey contract = contract.owner == pubKey || elem pubKey contract.parties

type ChildSlots
  = ()

data View
  = Home
  | WalletView PubKey

data Action
  = Init
  | ShowRightPanel Boolean
  | LoadContractFromSimulation
  | StartContract
  | ResetContract
  | ResetAll
  | NextSlot
  | ApplyTransaction
  | ChangeRoleOwner Int Party String
  | SelectWallet Wallet
  | AddInput Input (Array Bound)
  | RemoveInput Input
  | SetChoice ChoiceId ChosenNum
  | ChangeCurrencyInput Token BigInteger
  | AddCurrency Token
  | RenameWallet String
  | CreateWallet
  | SelectContract LoadedContract
  | ChangeHelpContext HelpContext

defaultEvent :: String -> Event
defaultEvent s = A.defaultEvent $ "Wallet." <> s

instance actionIsEvent :: IsEvent Action where
  toEvent Init = Just $ defaultEvent "Init"
  toEvent (ShowRightPanel _) = Just $ defaultEvent "ShowRightPanel"
  toEvent LoadContractFromSimulation = Just $ defaultEvent "LoadContractFromSimulation"
  toEvent StartContract = Just $ defaultEvent "StartContract"
  toEvent ResetContract = Just $ defaultEvent "ResetContract"
  toEvent ResetAll = Just $ defaultEvent "ResetAll"
  toEvent NextSlot = Just $ defaultEvent "NextSlot"
  toEvent ApplyTransaction = Just $ defaultEvent "ApplyTransaction"
  toEvent (ChangeRoleOwner _ _ _) = Just $ defaultEvent "ChangeRoleOwner"
  toEvent (SelectWallet _) = Just $ defaultEvent "SelectWallet"
  toEvent (AddInput _ _) = Just $ defaultEvent "AddInput"
  toEvent (RemoveInput _) = Just $ defaultEvent "RemoveInput"
  toEvent (SetChoice _ _) = Just $ defaultEvent "SetChoice"
  toEvent (ChangeCurrencyInput _ _) = Just $ defaultEvent "ChangeCurrencyInput"
  toEvent (AddCurrency _) = Just $ defaultEvent "AddCurrency"
  toEvent (RenameWallet _) = Just $ defaultEvent "RenameWallet"
  toEvent CreateWallet = Just $ defaultEvent "CreateWallet"
  toEvent (SelectContract _) = Just $ defaultEvent "SelectContract"
  toEvent (ChangeHelpContext _) = Just $ defaultEvent "ChangeHelpContext"

data Query a
  = LoadContract String a

data Message
  = SendContractToWallet

type State
  = { wallets :: Map String Wallet
    , view :: View
    , initialized :: Boolean
    , showRightPanel :: Boolean
    , loadContractError :: Maybe String
    , contracts :: Map Int LoadedContract
    , tokens :: Set Token
    , slot :: Slot
    , assetChanges :: Map Token BigInteger
    , addInputError :: Maybe String
    , helpContext :: HelpContext
    }

mkState :: State
mkState =
  { wallets: mempty
  , view: Home
  , initialized: false
  , showRightPanel: true
  , loadContractError: Nothing
  , contracts: mempty
  , tokens: Set.singleton (Token "" "")
  , slot: zero
  , assetChanges: mempty
  , addInputError: Nothing
  , helpContext: WalletsSimulatorHelp
  }

findWallet :: State -> PubKey -> Maybe Wallet
findWallet state walletName =
  let
    wallets :: Array Wallet
    wallets = state ^. (_wallets <<< to Map.values <<< to Array.fromFoldable)
  in
    find (\(Wallet { name }) -> name == walletName) wallets

_openWallet :: Lens' State (Maybe Wallet)
_openWallet = lens get' set'
  where
  get' state = do
    walletName <- case state ^. _view of
      WalletView w -> Just w
      _ -> Nothing
    findWallet state walletName

  set' state (Just wallet@(Wallet { name })) = case state ^. _view of
    WalletView walletName -> (set _view (WalletView name) <<< over _wallets (Map.insert name wallet)) state
    _ -> over _wallets (Map.insert name wallet) state

  set' state _ = state

_view :: Lens' State View
_view = prop (SProxy :: SProxy "view")

_wallets :: Lens' State (Map String Wallet)
_wallets = prop (SProxy :: SProxy "wallets")

_walletContracts :: PubKey -> Getter' State (Map Int LoadedContract)
_walletContracts pubKey = _contracts <<< to (Map.filter (isInvolvedInContract pubKey))

_runningContracts :: Getter' State (Map Int LoadedContract)
_runningContracts = _contracts <<< to (Map.filter _.started)

_walletLoadedContract :: Lens' State (Maybe LoadedContract)
_walletLoadedContract = lens get' set'
  where
  get' state = do
    idx <- state ^? (_openWallet <<< _Just <<< _loadedContract <<< _Just)
    Map.lookup idx state.contracts

  set' state (Just contract) =
    ( set (_openWallet <<< _Just <<< _loadedContract) (Just contract.idx)
        <<< set _contracts (Map.insert contract.idx contract state.contracts)
    )
      state

  set' state Nothing = set (_openWallet <<< _Just <<< _loadedContract) Nothing state

_currentLoadedMarloweState ::
  forall p.
  Strong p =>
  Choice p =>
  p MarloweState MarloweState ->
  p State State
_currentLoadedMarloweState = _walletLoadedContract <<< _Just <<< _marloweState <<< _Head

_loadedMarloweState ::
  forall p.
  Strong p =>
  Choice p =>
  p (NonEmptyList MarloweState) (NonEmptyList MarloweState) ->
  p State State
_loadedMarloweState = _walletLoadedContract <<< _Just <<< _marloweState

_started :: forall s. Lens' { started :: Boolean | s } Boolean
_started = prop (SProxy :: SProxy "started")

_initialized :: Lens' State Boolean
_initialized = prop (SProxy :: SProxy "initialized")

_showRightPanel :: Lens' State Boolean
_showRightPanel = prop (SProxy :: SProxy "showRightPanel")

_loadContractError :: Lens' State (Maybe String)
_loadContractError = prop (SProxy :: SProxy "loadContractError")

_contracts :: Lens' State (Map Int LoadedContract)
_contracts = prop (SProxy :: SProxy "contracts")

_tokens :: Lens' State (Set Token)
_tokens = prop (SProxy :: SProxy "tokens")

_assetChanges :: Lens' State (Map Token BigInteger)
_assetChanges = prop (SProxy :: SProxy "assetChanges")

_addInputError :: Lens' State (Maybe String)
_addInputError = prop (SProxy :: SProxy "addInputError")

_helpContext :: Lens' State HelpContext
_helpContext = prop (SProxy :: SProxy "helpContext")

mkComponent :: forall m. MonadEffect m => Component HTML Query Unit Message m
mkComponent =
  H.mkComponent
    { initialState: const mkState
    , render
    , eval:
      H.mkEval
        { handleAction: handleActionWithAnalyticsTracking handleAction
        , handleQuery
        , initialize: Just Init
        , receive: const Nothing
        , finalize: Nothing
        }
    }

applyTransactions :: forall m. MonadState State m => m Unit
applyTransactions = do
  initialPayments <- fromMaybe mempty <$> peruse (_currentLoadedMarloweState <<< _payments)
  modifying _loadedMarloweState (extendWith (updatePossibleActions <<< updateStateP))
  updatedPayments <- fromMaybe mempty <$> peruse (_currentLoadedMarloweState <<< _payments)
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
      for_ (fromTerm contractTerm) \contract -> do
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
              , marloweState: NEL.singleton (emptyMarloweState slot)
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
  assign _slot zero
  assign (_contracts <<< traversed <<< _started) false
  assign (_contracts <<< traversed <<< _marloweState) (NEL.singleton (emptyMarloweState zero))

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
    (extendWith (updatePossibleActions <<< over _slot (add one)))

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
        updateMarloweState (over _pendingInputs ((flip snoc) input))
      else
        assign _addInputError $ Just "Insufficient funds to add this input"

handleAction (AddInput input bounds) = do
  assign _addInputError Nothing
  let
    validChoice = case input of
      (IChoice _ chosenNum) -> inBounds chosenNum bounds
      _ -> true
  if validChoice then
    updateMarloweState (over _pendingInputs ((flip snoc) input))
  else
    assign _addInputError $ Just "Invalid Choice"

handleAction (RemoveInput input@(IDeposit _ _ token amount)) = do
  assign _addInputError Nothing
  modifying (_openWallet <<< _Just <<< _assets <<< ix token) (\v -> v + amount)
  updateMarloweState (over _pendingInputs (delete input))

handleAction (RemoveInput input) = do
  assign _addInputError Nothing
  updateMarloweState (over _pendingInputs (delete input))

handleAction (SetChoice choiceId chosenNum) = updateMarloweState (over _possibleActions (mapPartiesActionInput (updateChoice choiceId)))
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
    [ section [ classes [ panelSubHeader, aHorizontal ] ]
        [ div [ classes [ panelSubHeaderMain, aHorizontal ] ]
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
        , div [ classes [ panelSubHeaderSide, expanded (state ^. _showRightPanel) ] ]
            [ a [ classes [ (ClassName "drawer-icon-click") ], onClick $ const $ Just $ ShowRightPanel (state ^. (_showRightPanel <<< to not)) ]
                [ img [ src closeDrawerIcon, class_ (ClassName "drawer-icon") ] ]
            ]
        ]
    , section [ classes [ ClassName "code-panel", ClassName "full-height" ] ]
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
          [ classes [ ClassName "tooltip", ClassName "start-simulation-btn" ]
          , onClick $ const $ Just $ StartContract
          ]
          [ text "Start"
          ]
      , div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
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
      , div [ classes [ ClassName "code-editor", ClassName "expanded", ClassName "code" ] ]
          numberedText
      ]
      where
      numberedText = (HTML.code_ <<< Array.singleton <<< text) <$> split (Pattern "\n") contractString

  contractString =
    fromMaybe mempty do
      contract <-
        preview (_walletLoadedContract <<< _Just <<< _currentMarloweState <<< _contract <<< _Just) state
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
          <> [ div [ classes [ aHorizontal, ClassName "transaction-composer" ] ]
                [ h6 [ classes [ ClassName "input-composer-heading", noMargins ] ]
                    [ small [ classes [ textSecondaryColor, bold, uppercase ] ] [ text "Transaction Composer" ] ]
                , a [ onClick $ const $ Just $ ChangeHelpContext TransactionComposerHelp ] [ img [ src infoIcon, alt "info book icon" ] ]
                ]
            ]
          <> [ div [ classes [ ClassName "transaction-composer", ClassName "composer" ] ]
                ( if hasTransactions then
                    [ transactionComposer state
                    , div [ class_ (ClassName "transaction-btns") ]
                        [ ul [ classes [ ClassName "demo-list", aHorizontal ] ]
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
  pendingInputs = fromMaybe mempty (state ^? (_currentLoadedMarloweState <<< _pendingInputs))

  possibleActions =
    fromMaybe mempty
      $ state
      ^? ( _currentLoadedMarloweState
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

  hasTransactions = has (_currentLoadedMarloweState <<< _pendingInputs <<< to Array.null <<< to not) state

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
  div [ classes [ Classes.panelContents, active, ClassName "wallet-composer-state" ] ]
    [ div [ classes [ rTable, rTable4cols ] ]
        ( warningsRow <> errorRow
            <> dataRow "Expiration Slot" (state ^. (_currentLoadedMarloweState <<< _contract <<< to contractMaxTime))
            <> tableRow
                { title: "Accounts"
                , emptyMessage: "No accounts have been used"
                , columns: ("Account ID" /\ "Participant" /\ "Assets")
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

  warnings = state ^. (_currentLoadedMarloweState <<< _transactionWarnings)

  warningsRow =
    if Array.null warnings then
      []
    else
      (headerRow "Warnings" ("type" /\ "details" /\ mempty)) <> foldMap displayWarning' warnings

  errorRow = case state ^? (_currentLoadedMarloweState <<< _transactionError) of
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
      (accounts :: Array _) = state ^. (_currentLoadedMarloweState <<< _state <<< _accounts <<< to Map.toUnfoldable)

      asTuple (Tuple (Tuple (AccountId accountNumber accountOwner) token) value) = show accountNumber /\ stripParens (show accountOwner) /\ (show value <> " " <> shortTokenString token)
    in
      map asTuple accounts

  shortTokenString (Token "" "") = "Ada"

  shortTokenString (Token currSym tokName) = currSym <> " " <> tokName

  choicesData =
    let
      (choices :: Array _) = state ^. (_currentLoadedMarloweState <<< _state <<< _choices <<< to Map.toUnfoldable)

      asTuple (Tuple (ChoiceId choiceName choiceOwner) value) = show choiceName /\ stripParens (show choiceOwner) /\ show value
    in
      map asTuple choices

  paymentsData =
    let
      payments = state ^. (_currentLoadedMarloweState <<< _payments)

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
      (bindings :: Array _) = state ^. (_currentLoadedMarloweState <<< _state <<< _boundValues <<< to Map.toUnfoldable)

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

  displayWarning' (TransactionNonPositiveDeposit party (AccountId accNum owner) tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositiveDeposit" ]
    , div [ class_ rTableCell ]
        [ text $ "Party " <> show party <> " is asked to deposit " <> show amount
            <> " units of "
            <> show tok
            <> " into account "
            <> show accNum
            <> " of "
            <> show owner
            <> "."
        ]
    ]

  displayWarning' (TransactionNonPositivePay (AccountId accNum owner) payee tok amount) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionNonPositivePay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show amount
            <> " units of "
            <> show tok
            <> " from account "
            <> show accNum
            <> " of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account (AccountId accNum2 owner2)) -> "account " <> show accNum2 <> " of " <> show owner2
                  (Party dest) -> "party " <> show dest
              )
            <> "."
        ]
    ]

  displayWarning' (TransactionPartialPay (AccountId accNum owner) payee tok amount expected) =
    [ div [ classes [ rTableCell, first ] ] []
    , div [ class_ (ClassName "RTable-2-cells") ] [ text "TransactionPartialPay" ]
    , div [ class_ (ClassName "RTable-4-cells") ]
        [ text $ "The contract is supposed to make a payment of "
            <> show expected
            <> " units of "
            <> show tok
            <> " from account "
            <> show accNum
            <> " of "
            <> show owner
            <> " to "
            <> ( case payee of
                  (Account (AccountId accNum2 owner2)) -> ("account " <> show accNum2 <> " of " <> show owner2)
                  (Party dest) -> ("party " <> show dest)
              )
            <> " but there is only "
            <> show amount
            <> "."
        ]
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
    div [ classes [ panelSubHeaderMain, aHorizontal ] ]
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
    [ classes [ aHorizontal, ClassName "flex-wrap", ClassName "choice-row" ] ]
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
  State ->
  HTML p Action
transactionComposer state =
  ul [ class_ (ClassName "participants") ]
    if Array.null pendingInputs then
      [ text "Empty transaction" ]
    else
      [ transaction state ]
  where
  currentBlock = state ^? (_currentLoadedMarloweState <<< _slot)

  pendingInputs = fromMaybe mempty (state ^? (_currentLoadedMarloweState <<< _pendingInputs))

transaction ::
  forall p.
  State ->
  HTML p Action
transaction state =
  li [ classes [ ClassName "participant-a", noMargins ] ]
    [ ul
        []
        (map (transactionRow state) (state ^. (_currentLoadedMarloweState <<< _pendingInputs)))
    ]

transactionRow ::
  forall p.
  State ->
  Input ->
  HTML p Action
transactionRow state input@(IDeposit (AccountId accountNumber accountOwner) party token money) =
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
