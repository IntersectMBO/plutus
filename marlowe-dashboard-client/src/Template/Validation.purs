module Template.Validation
  ( ContractNicknameError(..)
  , contractNicknameError
  , RoleError(..)
  , roleError
  , SlotError(..)
  , slotError
  , ValueError(..)
  , valueError
  ) where

import Prelude
import Data.Map (member)
import Data.Maybe (Maybe(..))
import InputField.Types (class InputFieldError)
import Marlowe.Semantics (Slot)
import Marlowe.Slot (dateTimeStringToSlot)
import WalletData.Types (WalletLibrary)

data ContractNicknameError
  = EmptyContractNickname

derive instance eqContractNicknameError :: Eq ContractNicknameError

instance inputFieldErrorContractNicknameError :: InputFieldError ContractNicknameError where
  inputErrorToString EmptyContractNickname = "Contract nickname cannot be blank"

contractNicknameError :: String -> Maybe ContractNicknameError
contractNicknameError "" = Just EmptyContractNickname

contractNicknameError _ = Nothing

----------
data RoleError
  = EmptyNickname
  | NonExistentNickname

derive instance eqRoleError :: Eq RoleError

instance inputFieldErrorRoleError :: InputFieldError RoleError where
  inputErrorToString EmptyNickname = "Role nickname cannot be blank"
  inputErrorToString NonExistentNickname = "Nickname not found in your wallet library"

roleError :: WalletLibrary -> String -> Maybe RoleError
roleError _ "" = Just EmptyNickname

roleError walletLibrary walletNickname =
  if member walletNickname walletLibrary then
    Nothing
  else
    Just NonExistentNickname

----------
data SlotError
  = EmptySlot
  | PastSlot
  | BadDateTimeString

derive instance eqSlotError :: Eq SlotError

instance inputFieldErrorSlotError :: InputFieldError SlotError where
  inputErrorToString EmptySlot = "Timeout cannot be blank"
  inputErrorToString PastSlot = "Timeout date is past"
  inputErrorToString BadDateTimeString = "Invalid timeout"

-- note: we validate slot inputs against the dateTimeString that we get from HTML
slotError :: Slot -> String -> Maybe SlotError
slotError _ "" = Just EmptySlot

slotError currentSlot dateTimeString = case dateTimeStringToSlot dateTimeString of
  Just slot ->
    if slot <= currentSlot then
      Just PastSlot
    else
      Nothing
  Nothing -> Just BadDateTimeString

----------
data ValueError
  = EmptyValue

derive instance eqValueError :: Eq ValueError

instance inputFieldErrorValueError :: InputFieldError ValueError where
  inputErrorToString EmptyValue = "Value cannot be blank"

valueError :: String -> Maybe ValueError
valueError "" = Just EmptyValue

valueError _ = Nothing
