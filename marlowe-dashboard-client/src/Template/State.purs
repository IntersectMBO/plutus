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
import Data.Lens (assign, modifying)
import Data.Map (Map, insert, fromFoldable)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set (map, mapMaybe) as Set
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Halogen (HalogenM)
import MainFrame.Lenses (_templateState, _walletState)
import MainFrame.Types (ChildSlots, Msg)
import MainFrame.Types (Action, State) as MainFrame
import Marlowe.Extended (Contract, getParties, getPlaceholderIds, initializeTemplateContent, typeToLens)
import Marlowe.Semantics (Party(..))
import Template.Lenses (_contractNickname, _roleWallets, _templateContent)
import Template.Library (defaultTemplate)
import Template.Types (Action(..), State, Template)

defaultState :: State
defaultState = mkInitialState defaultTemplate

mkInitialState :: Template -> State
mkInitialState template =
  { template: template
  , contractNickname: template.metaData.contractName
  , roleWallets: mkRoleWallets template.extendedContract
  , templateContent: initializeTemplateContent $ getPlaceholderIds template.extendedContract
  }

mkRoleWallets :: Contract -> Map String String
mkRoleWallets contract = fromFoldable $ Set.map (\name -> Tuple name "") (getRoleNames contract)

getRoleNames :: Contract -> Set String
getRoleNames contract = Set.mapMaybe roleName (getParties contract)
  where
  roleName (PK pubKey) = Nothing

  roleName (Role tokenName) = Just tokenName

handleAction :: forall m. MonadAff m => Action -> HalogenM MainFrame.State MainFrame.Action ChildSlots Msg m Unit
handleAction (SetContractNickname nickname) = assign (_walletState <<< _templateState <<< _contractNickname) nickname

handleAction (SetRoleWallet roleName walletNickname) = modifying (_walletState <<< _templateState <<< _roleWallets) $ insert roleName walletNickname

handleAction (SetParameter integerTemplateType key mValue) = do
  let
    value = fromMaybe zero mValue
  modifying (_walletState <<< _templateState <<< _templateContent <<< typeToLens integerTemplateType) $ insert key value
