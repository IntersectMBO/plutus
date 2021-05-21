module Template.Validation
  ( RoleError(..)
  , ParameterError(..)
  , roleError
  , slotError
  , valueError
  , roleWalletsAreValid
  , templateContentIsValid
  ) where

-- General note: Validating number inputs is a pain. I cannot find a nice way
-- of checking that number inputs are non-empty, or that they are integers (as
-- opposed to rationals). It would almost be simpler to give all inputs a 
-- type="text", and validate against the string input before converting it to
-- a number. But then the HTML interface wouldn't be as user-friendly. :(
import Prelude
import Data.BigInteger (BigInteger)
import Data.Map (Map, isEmpty, mapMaybe, member)
import Data.Maybe (Maybe(..))
import InputField.Types (class InputFieldError, State)
import InputField.State (validate)
import Marlowe.Extended (TemplateContent(..))
import Marlowe.Semantics (Slot, TokenName)
import Marlowe.Slot (dateTimeStringToSlot)
import WalletData.Types (WalletLibrary)

data RoleError
  = EmptyNickname
  | NonExistentNickname

derive instance eqRoleError :: Eq RoleError

instance inputFieldErrorRoleError :: InputFieldError RoleError where
  inputErrorToString EmptyNickname = "Role nickname cannot be blank"
  inputErrorToString NonExistentNickname = "Nickname not found in your wallet library"

data ParameterError
  = EmptyTimeout
  | PastTimeout
  | BadDateTimeString

derive instance eqParameterError :: Eq ParameterError

instance inputFieldErrorParameterError :: InputFieldError ParameterError where
  inputErrorToString EmptyTimeout = "Timeout cannot be blank"
  inputErrorToString PastTimeout = "Timeout date is past"
  inputErrorToString BadDateTimeString = "Invalid timeout"

roleError :: WalletLibrary -> String -> Maybe RoleError
roleError _ "" = Just EmptyNickname

roleError walletLibrary walletNickname =
  if member walletNickname walletLibrary then
    Nothing
  else
    Just NonExistentNickname

-- note: we validate slot inputs against the dateTimeString that we get from HTML
slotError :: Slot -> String -> Maybe ParameterError
slotError _ "" = Just EmptyTimeout

slotError currentSlot dateTimeString = case dateTimeStringToSlot dateTimeString of
  Just slot ->
    if slot <= currentSlot then
      Just PastTimeout
    else
      Nothing
  Nothing -> Just BadDateTimeString

-- placeholder in case we add value validation in the future
valueError :: BigInteger -> Maybe ParameterError
valueError _ = Nothing

------------------------------------------------------------
roleWalletsAreValid :: Map TokenName (State RoleError) -> Boolean
roleWalletsAreValid roleWallets = isEmpty $ mapMaybe (\input -> validate input) roleWallets

templateContentIsValid :: TemplateContent -> Map String String -> Slot -> Boolean
templateContentIsValid (TemplateContent { valueContent }) slotContentStrings currentSlot =
  (isEmpty $ mapMaybe (\value -> slotError currentSlot value) slotContentStrings)
    && (isEmpty $ mapMaybe (\value -> valueError value) valueContent)
