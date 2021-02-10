module Contact.Types
  ( State
  , ContactKey
  , Contact(..)
  , PubKeyHash
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Map (Map)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple)
import Foreign.Generic (class Decode, class Encode, defaultOptions, genericDecode, genericEncode)

type State
  = { contacts :: Map ContactKey Contact
    , newContactKey :: ContactKey
    }

type ContactKey
  = Tuple String PubKeyHash

newtype Contact
  = Contact
  { userHasPickedUp :: Boolean
  }

derive instance newtypeContact :: Newtype Contact _

derive instance eqContact :: Eq Contact

derive instance genericContact :: Generic Contact _

instance encodeContact :: Encode Contact where
  encode = genericEncode defaultOptions

instance decodeContact :: Decode Contact where
  decode = genericDecode defaultOptions

-- TODO: import PubKeyHash
type PubKeyHash
  = String

data Action
  = ToggleNewContactCard
  | ToggleEditContactCard ContactKey
  | SetNewContactKey PubKeyHash
  | SetNewContactNickname String
  | AddNewContact

-- | Here we decide which top-level queries to track as GA events, and
-- how to classify them.
instance actionIsEvent :: IsEvent Action where
  toEvent ToggleNewContactCard = Just $ defaultEvent "ToggleNewContactCard"
  toEvent (ToggleEditContactCard _) = Just $ defaultEvent "ToggleEditContactCard"
  toEvent (SetNewContactKey _) = Just $ defaultEvent "SetNewContactKey"
  toEvent (SetNewContactNickname _) = Just $ defaultEvent "SetNewContactNickname"
  toEvent AddNewContact = Just $ defaultEvent "AddNewContact"
