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
import Data.Lens (assign, modifying)
import Data.Map (Map, insert, fromFoldable)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (mapMaybe) as Set
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Env (Env)
import Halogen (HalogenM)
import MainFrame.Lenses (_playState)
import MainFrame.Types (Action, State) as MainFrame
import MainFrame.Types (ChildSlots, Msg)
import Marlowe.Extended (Contract, ContractTemplate, getParties, getPlaceholderIds, initializeTemplateContent, typeToLens)
import Marlowe.Market.Contract1 (contractTemplate)
import Marlowe.Semantics (Party(..))
import Play.Lenses (_templateState)
import Template.Lenses (_contractNickname, _roleWallets, _templateContent)
import Template.Types (Action(..), State)

defaultState :: State
defaultState = mkInitialState contractTemplate

mkInitialState :: ContractTemplate -> State
mkInitialState template =
  { template: template
  , contractNickname: template.metaData.contractName
  , roleWallets: mkRoleWallets template.extendedContract
  , templateContent: initializeTemplateContent $ getPlaceholderIds template.extendedContract
  }

mkRoleWallets :: Contract -> Map String String
mkRoleWallets contract = fromFoldable $ Set.mapMaybe getRoleEntry (getParties contract)
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

handleAction (SetParameter integerTemplateType key mValue) = do
  let
    value = fromMaybe zero mValue
  modifying (_playState <<< _templateState <<< _templateContent <<< typeToLens integerTemplateType) $ insert key value

-- all other actions are handled in `Play.State`
handleAction _ = pure unit
