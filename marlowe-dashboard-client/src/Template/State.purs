module Template.State
  ( dummyState
  , mkInitialState
  , handleAction
  , instantiateExtendedContract
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Array (mapMaybe)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, use, view)
import Data.Map (Map, insert, keys)
import Data.Map (fromFoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (toUnfoldable) as Set
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Examples.PureScript.Escrow (contractTemplate)
import Halogen (HalogenM)
import Halogen.Extra (mapMaybeSubmodule, mapSubmodule)
import InputField.State (dummyState, handleAction, initialState) as InputField
import InputField.Types (Action(..), State) as InputField
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (Contract) as Extended
import Marlowe.Extended (resolveRelativeTimes, toCore)
import Marlowe.Extended.Metadata (ContractTemplate, lovelaceFormat)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics (Contract) as Semantic
import Marlowe.Semantics (Party(..), Slot(..), TokenName)
import Marlowe.Slot (dateTimeStringToSlot)
import Marlowe.Template (TemplateContent, fillTemplate, getPlaceholderIds, _slotContent, _valueContent, initializeTemplateContent)
import Template.Lenses (_contractNickname, _dummyNumberInput, _roleWalletInput, _roleWalletInputs, _slotContentStrings, _templateContent)
import Template.Types (Action(..), State)
import Template.Validation (RoleError, roleError)

-- see note [dummyState] in MainFrame.State
dummyState :: State
dummyState = mkInitialState contractTemplate

mkInitialState :: ContractTemplate -> State
mkInitialState template =
  let
    templateContent = initializeTemplateContent $ getPlaceholderIds template.extendedContract
  in
    { template: template
    , contractNickname: template.metaData.contractName
    , roleWalletInputs: mkRoleWalletInputs template.extendedContract
    , templateContent
    -- slot content is input as a datetime input, the value of which is a string :(
    -- so we need to keep a copy of that string value around
    , slotContentStrings: map (const "") $ view _slotContent templateContent
    , dummyNumberInput: InputField.initialState $ Just lovelaceFormat
    }

mkRoleWalletInputs :: Extended.Contract -> Map TokenName (InputField.State RoleError)
mkRoleWalletInputs contract = Map.fromFoldable $ mapMaybe getRoleInput (Set.toUnfoldable $ getParties contract)
  where
  getRoleInput :: Party -> Maybe (Tuple TokenName (InputField.State RoleError))
  getRoleInput (PK pubKey) = Nothing

  getRoleInput (Role tokenName) = Just (Tuple tokenName $ InputField.initialState Nothing)

-- Some actions are handled in `Dashboard.State` because they involve
-- modifications of that state. See Note [State] in MainFrame.State.
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (SetTemplate contractTemplate) = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

handleAction OpenTemplateLibraryCard = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

handleAction (OpenCreateWalletCard tokenName) = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

handleAction OpenSetupConfirmationCard = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

handleAction CloseSetupConfirmationCard = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

handleAction (SetContractNickname nickname) = assign _contractNickname nickname

handleAction (UpdateRoleWalletValidators walletLibrary) = do
  roleWalletInputs <- use _roleWalletInputs
  let
    roleTokens :: Array TokenName
    roleTokens = Set.toUnfoldable $ keys roleWalletInputs
  void
    $ for roleTokens \tokenName ->
        handleAction $ RoleWalletInputAction tokenName $ InputField.SetValidator $ roleError walletLibrary

handleAction (RoleWalletInputAction tokenName inputFieldAction) = toRoleWalletInput tokenName $ InputField.handleAction inputFieldAction

handleAction (SetSlotContent key dateTimeString) = do
  -- TODO: this assumes dateTimeString represents a UTC DateTime, but users will expect
  -- to input a _local_ DateTime, so we should convert based on the user's timezone
  for_ (dateTimeStringToSlot dateTimeString) \(Slot slot) ->
    modifying (_templateContent <<< _slotContent) $ insert key slot
  modifying (_slotContentStrings) $ insert key dateTimeString

handleAction (SetValueContent key mValue) = modifying (_templateContent <<< _valueContent) $ insert key $ fromMaybe zero mValue

handleAction (DummyNumberInputAction inputFieldAction) = toDummyNumberInput $ InputField.handleAction inputFieldAction

handleAction StartContract = pure unit -- handled in Dashboard.State (see note [State] in MainFrame.State)

instantiateExtendedContract :: Slot -> Extended.Contract -> TemplateContent -> Maybe Semantic.Contract
instantiateExtendedContract currentSlot extendedContract templateContent =
  let
    relativeContract = resolveRelativeTimes currentSlot extendedContract
  in
    toCore $ fillTemplate templateContent relativeContract

------------------------------------------------------------
toRoleWalletInput ::
  forall m msg slots.
  Functor m =>
  TokenName ->
  HalogenM (InputField.State RoleError) (InputField.Action RoleError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toRoleWalletInput tokenName = mapMaybeSubmodule (_roleWalletInput tokenName) (RoleWalletInputAction tokenName) InputField.dummyState

toDummyNumberInput ::
  forall m msg slots.
  Functor m =>
  HalogenM (InputField.State RoleError) (InputField.Action RoleError) slots msg m Unit ->
  HalogenM State Action slots msg m Unit
toDummyNumberInput = mapSubmodule _dummyNumberInput DummyNumberInputAction
