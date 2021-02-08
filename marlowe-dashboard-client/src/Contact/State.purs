module Contact.State
  ( initialState
  , handleAction
  ) where

import Prelude
import Contact.Lenses (_contacts, _key, _newContact, _nickname)
import Contact.Types (Action(..), Contact(..), State)
import Data.Array (find)
import Data.Lens (assign, modifying, use, view)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Foreign.Generic (encodeJSON)
import Halogen (HalogenM, liftEffect)
import LocalStorage (setItem)
import MainFrame.Types (ChildSlots, Msg)
import StaticData (contactsLocalStorageKey)

initialState :: State
initialState =
  { contacts: []
  , newContact: emptyContact
  }

emptyContact :: Contact
emptyContact = Contact { key: "", nickname: "" }

handleAction :: forall m. MonadAff m => Action -> HalogenM State Action ChildSlots Msg m Unit
handleAction ToggleNewContactCard = pure unit -- handled in MainFrame.State

handleAction (ToggleEditContactCard contact) = pure unit -- handled in MainFrame.State

handleAction (SetNewContactKey key) = do
  nickname <- use (_newContact <<< _nickname)
  assign _newContact $ Contact { key, nickname }

handleAction (SetNewContactNickname nickname) = do
  key <- use (_newContact <<< _key)
  assign _newContact $ Contact { key, nickname }

handleAction AddNewContact = do
  oldContacts <- use _contacts
  newContact <- use _newContact
  key <- use (_newContact <<< _key)
  case find (\contact -> view _key contact == key) oldContacts of
    Nothing -> do
      modifying _contacts $ append [ newContact ]
      assign _newContact emptyContact
      newContacts <- use _contacts
      liftEffect $ setItem contactsLocalStorageKey $ encodeJSON newContacts
    _ -> pure unit
