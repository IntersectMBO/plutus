module Template.Validation
  ( RoleError(..)
  , ParameterError(..)
  , roleError
  , slotError
  , valueError
  , roleWalletsAreValid
  ) where

-- General note: Validating number inputs is a pain. I cannot find a nice way
-- of checking that number inputs are non-empty, or that they are integers (as
-- opposed to rationals). It would almost be simpler to give all inputs a 
-- type="text", and validate against the string input before converting it to
-- a number. But then the HTML interface wouldn't be as user-friendly. :(
import Prelude
import Data.BigInteger (BigInteger)
import Data.Map (Map, isEmpty, mapMaybe, member)
import Data.Map.Extra (mapIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import WalletData.Types (WalletLibrary)

data RoleError
  = EmptyNickname
  | NonExistentNickname

derive instance eqRoleError :: Eq RoleError

instance showRoleError :: Show RoleError where
  show EmptyNickname = "Role nickname cannot be blank"
  show NonExistentNickname = "Nickname not found in your wallet library"

data ParameterError
  = NonPositiveTimeout

derive instance eqParameterError :: Eq ParameterError

instance showParameterError :: Show ParameterError where
  show NonPositiveTimeout = "Timeout must be positive"

roleError :: String -> WalletLibrary -> Maybe RoleError
roleError "" _ = Just EmptyNickname

roleError nickname wallets =
  if member nickname $ mapIndex fst wallets then
    Nothing
  else
    Just NonExistentNickname

slotError :: BigInteger -> Maybe ParameterError
slotError timeout =
  if timeout <= zero then
    Just NonPositiveTimeout
  else
    Nothing

-- placeholder in case we add value validation in the future
valueError :: BigInteger -> Maybe ParameterError
valueError _ = Nothing

roleWalletsAreValid :: Map String String -> WalletLibrary -> Boolean
roleWalletsAreValid roleWallets wallets = isEmpty $ mapMaybe (\value -> roleError value wallets) roleWallets
