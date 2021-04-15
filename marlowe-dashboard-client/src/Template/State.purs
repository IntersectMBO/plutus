module Template.State
  ( dummyState
  , mkInitialState
  , handleAction
  ) where

import Prelude
import Control.Monad.Reader (class MonadAsk)
import Data.Foldable (for_)
import Data.Lens (assign, modifying, view)
import Data.Map (Map, insert)
import Data.Map (fromFoldable) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (mapMaybe) as Set
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM)
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (Contract, _slotContent, _valueContent, getPlaceholderIds, initializeTemplateContent)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.HasParties (getParties)
import Examples.PureScript.Escrow (contractTemplate)
import Marlowe.Semantics (Party(..), Slot(..))
import Marlowe.Slot (dateTimeStringToSlot)
import Template.Lenses (_contractNickname, _roleWallets, _slotContentStrings, _templateContent)
import Template.Types (Action(..), State)

-- see note [dummyState]
dummyState :: State
dummyState = mkInitialState contractTemplate

mkInitialState :: ContractTemplate -> State
mkInitialState template =
  let
    templateContent = initializeTemplateContent $ getPlaceholderIds template.extendedContract
  in
    { template: template
    , contractNickname: template.metaData.contractName
    , roleWallets: mkRoleWallets template.extendedContract
    , templateContent
    -- slot content is input as a datetime input, the value of whic is a string :(
    -- so we need to keep a copy of that string value around
    , slotContentStrings: map (const "") $ view _slotContent templateContent
    }

mkRoleWallets :: Contract -> Map String String
mkRoleWallets contract = Map.fromFoldable $ Set.mapMaybe getRoleEntry (getParties contract)
  where
  getRoleEntry (PK pubKey) = Nothing

  getRoleEntry (Role tokenName) = Just (Tuple tokenName "")

-- Some actions are handled in `Play.State` because they involve
-- modifications of that state. See Note [State].
handleAction ::
  forall m.
  MonadAff m =>
  MonadAsk Env m =>
  Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction (SetTemplate contractTemplate) = pure unit -- handled in Play.State (see note [State])

handleAction OpenTemplateLibraryCard = pure unit -- handled in Play.State (see note [State])

handleAction (OpenCreateWalletCard tokenName) = pure unit -- handled in Play.State (see note [State])

handleAction OpenSetupConfirmationCard = pure unit -- handled in Play.State (see note [State])

handleAction CloseSetupConfirmationCard = pure unit -- handled in Play.State (see note [State])

handleAction (SetContractNickname nickname) = assign _contractNickname nickname

handleAction (SetRoleWallet roleName walletNickname) = modifying _roleWallets $ insert roleName walletNickname

handleAction (SetSlotContent key dateTimeString) = do
  -- TODO: this assumes dateTimeString represents a UTC DateTime, but users will expect
  -- to input a _local_ DateTime, so we should convert based on the user's timezone
  for_ (dateTimeStringToSlot dateTimeString) \(Slot slot) ->
    modifying (_templateContent <<< _slotContent) $ insert key slot
  modifying (_slotContentStrings) $ insert key dateTimeString

handleAction (SetValueContent key mValue) = modifying (_templateContent <<< _valueContent) $ insert key $ fromMaybe zero mValue

handleAction StartContract = pure unit -- handled in Play.State (see note [State])
