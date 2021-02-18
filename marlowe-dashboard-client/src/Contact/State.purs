module Contact.State
  ( initialState
  , handleAction
  ) where

import Prelude
import Contact.Lenses (_contacts, _newContactKey)
import Contact.Types (Action(..), Contact(..), State)
import Data.Lens (assign, modifying, use)
import Data.Lens.Lens.Tuple (_1, _2)
import Data.Map (empty, insert, member)
import Data.Tuple (Tuple(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect)
import LocalStorage (setItem)
import MainFrame.Types (ChildSlots, Msg)
import StaticData (contactsLocalStorageKey)

initialState :: State
initialState =
  { contacts: empty
  , newContactKey: Tuple "" ""
  }

emptyContact :: Contact
emptyContact = Contact { userHasPickedUp: false }

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction ToggleNewContactCard = pure unit -- handled in MainFrame.State

handleAction (ToggleEditContactCard contact) = pure unit -- handled in MainFrame.State

handleAction (SetNewContactNickname nickname) = assign (_newContactKey <<< _1) nickname

handleAction (SetNewContactKey key) = assign (_newContactKey <<< _2) key

handleAction AddNewContact = do
  oldContacts <- use _contacts
  newContactKey <- use _newContactKey
  if not $ member newContactKey oldContacts then do
    modifying _contacts $ insert newContactKey emptyContact
    assign _newContactKey $ Tuple "" ""
    newContacts <- use _contacts
    liftEffect $ setItem contactsLocalStorageKey $ encodeJSON newContacts
  else
    pure unit
