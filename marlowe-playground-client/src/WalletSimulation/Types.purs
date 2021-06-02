module WalletSimulation.Types where

import Prelude hiding (div)
import Analytics (class IsEvent, Event)
import Analytics as A
import Data.Array (elem, find)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Lens (Getter', Lens', _Just, lens, over, set, to, (^.), (^?))
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.NonEmptyList (_Head)
import Data.Lens.Record (prop)
import Data.List.Types (NonEmptyList)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Profunctor.Choice (class Choice)
import Data.Profunctor.Strong (class Strong)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Help (HelpContext(..))
import Marlowe.Semantics (Bound, ChoiceId, ChosenNum, Input, Party, PubKey, Slot, Token(..))
import Marlowe.Semantics as S
import Simulator.Types (MarloweState)
import Simulator.Lenses (_marloweState)

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
