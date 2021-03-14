module Template.State
  ( defaultState
  , mkInitialState
  , handleAction
  ) where

-- Note: There is no independent template state as such (just a property of
-- the main state). This module simply includes some template-related helper
-- functions for use in MainFrame.Sate, separated out to keep modules
-- relatively small and easier to read.
-- Maybe we could do the same for Contract.State...?
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
import MainFrame.Lenses (_playState)
import MainFrame.Types (Action, State) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (Contract, _slotContent, _valueContent, getPlaceholderIds, initializeTemplateContent)
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.HasParties (getParties)
import Marlowe.Market.Contract1 (contractTemplate)
import Marlowe.Semantics (Party(..), Slot(..))
import Marlowe.Slot (dateTimeStringToSlot)
import Play.Lenses (_templateState)
import Template.Lenses (_contractNickname, _roleWallets, _slotContentStrings, _templateContent)
import Template.Types (Action(..), State)

defaultState :: State
defaultState = mkInitialState contractTemplate

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
  Action -> HalogenM MainFrame.State MainFrame.Action ChildSlots Msg m Unit
handleAction (SetContractNickname nickname) = assign (_playState <<< _templateState <<< _contractNickname) nickname

handleAction (SetRoleWallet roleName walletNickname) = modifying (_playState <<< _templateState <<< _roleWallets) $ insert roleName walletNickname

handleAction (SetSlotContent key dateTimeString) = do
  -- TODO: this assumes dateTimeString represents a UTC DateTime, but users will expect
  -- to input a _local_ DateTime, so we should convert based on the user's timezone
  for_ (dateTimeStringToSlot dateTimeString) \(Slot slot) ->
    modifying (_playState <<< _templateState <<< _templateContent <<< _slotContent) $ insert key slot
  modifying (_playState <<< _templateState <<< _slotContentStrings) $ insert key dateTimeString

handleAction (SetValueContent key mValue) = modifying (_playState <<< _templateState <<< _templateContent <<< _valueContent) $ insert key $ fromMaybe zero mValue

-- all other actions are handled in `Play.State`
handleAction _ = pure unit
