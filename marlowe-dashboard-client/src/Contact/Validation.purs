module Contact.Validation
  ( KeyError(..)
  , NicknameError(..)
  , keyError
  , nicknameError
  ) where

import Prelude
import Contact.Lenses (_key, _nickname)
import Contact.Types (Contact, PubKeyHash)
import Data.Array (find)
import Data.Lens (view)
import Data.Maybe (Maybe(..))

data KeyError
  = EmptyKey
  | DuplicateKey

derive instance eqKeyError :: Eq KeyError

instance showKeyError :: Show KeyError where
  show EmptyKey = "Wallet key cannot be blank"
  show DuplicateKey = "Wallet key is already in your contacts"

data NicknameError
  = EmptyNickname
  | DuplicateNickname

derive instance eqNicknameError :: Eq NicknameError

instance showNicknameError :: Show NicknameError where
  show EmptyNickname = "Nickname cannot be blank"
  show DuplicateNickname = "Nickname is already in use in your contacts"

keyError :: PubKeyHash -> Array Contact -> Maybe KeyError
keyError "" _ = Just EmptyKey

keyError key contacts =
  if find (\contact -> view _key contact == key) contacts == Nothing then
    Nothing
  else
    Just DuplicateKey

nicknameError :: String -> Array Contact -> Maybe NicknameError
nicknameError "" _ = Just EmptyNickname

nicknameError nickname contacts =
  if find (\contact -> view _nickname contact == nickname) contacts == Nothing then
    Nothing
  else
    Just DuplicateNickname
