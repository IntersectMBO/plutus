module WalletData.Types
  ( State
  , WalletLibrary
  , WalletNickname
  , WalletDetails
  , WalletInfo(..)
  , Wallet(..)
  , PubKeyHash(..)
  , CardSection(..)
  , WalletNicknameError(..)
  , WalletIdError(..)
  , Action(..)
  ) where

import Prelude
import Analytics (class IsEvent, defaultEvent, toEvent)
import Clipboard (Action) as Clipboard
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import InputField.Types (Action, State) as InputField
import InputField.Types (class InputFieldError)
import Marlowe.PAB (MarloweData, MarloweParams, PlutusAppId)
import Marlowe.Semantics (Assets, PubKey)
import Types (WebData)

type State
  = { walletLibrary :: WalletLibrary
    , cardSection :: CardSection
    , walletNicknameInput :: InputField.State WalletNicknameError
    , walletIdInput :: InputField.State WalletIdError
    , remoteWalletInfo :: WebData WalletInfo
    }

type WalletLibrary
  = Map WalletNickname WalletDetails

type WalletNickname
  = String

type WalletDetails
  = { walletNickname :: WalletNickname
    , companionAppId :: PlutusAppId
    , marloweAppId :: PlutusAppId
    , walletInfo :: WalletInfo
    , assets :: Assets
    -- this property shouldn't be necessary, but at the moment we are getting too many update notifications
    -- through the PAB - so until that bug is fixed, we use this to check whether an update notification
    -- really has changed anything
    , previousCompanionAppState :: Maybe (Map MarloweParams MarloweData)
    }

-- this is the data that the wallet API returns when creating a wallet and when subsequently requesting
-- its "own-public-key"
newtype WalletInfo
  = WalletInfo
  { wallet :: Wallet
  , pubKey :: PubKey
  , pubKeyHash :: PubKeyHash
  }

derive instance newtypeWalletInfo :: Newtype WalletInfo _

derive instance eqWalletInfo :: Eq WalletInfo

derive instance genericWalletInfo :: Generic WalletInfo _

instance encodeWalletInfo :: Encode WalletInfo where
  encode value = genericEncode defaultOptions value

instance decodeWalletInfo :: Decode WalletInfo where
  decode value = genericDecode defaultOptions value

newtype Wallet
  = Wallet BigInteger

derive instance newtypeWallet :: Newtype Wallet _

derive instance eqWallet :: Eq Wallet

derive instance genericWallet :: Generic Wallet _

instance encodeWallet :: Encode Wallet where
  encode value = genericEncode defaultOptions value

instance decodeWallet :: Decode Wallet where
  decode value = genericDecode defaultOptions value

-- TODO: move this into Marlowe.Semantics
newtype PubKeyHash
  = PubKeyHash String

derive instance newtypePubKeyHash :: Newtype PubKeyHash _

derive instance eqPubKeyHash :: Eq PubKeyHash

derive instance genericPubKeyHash :: Generic PubKeyHash _

instance encodePubKeyHash :: Encode PubKeyHash where
  encode value = genericEncode defaultOptions value

instance decodePubKeyHash :: Decode PubKeyHash where
  decode value = genericDecode defaultOptions value

data CardSection
  = Home
  | ViewWallet WalletDetails
  | NewWallet (Maybe String)

derive instance eqCardSection :: Eq CardSection

data WalletNicknameError
  = EmptyWalletNickname
  | DuplicateWalletNickname
  | BadWalletNickname

derive instance eqWalletNicknameError :: Eq WalletNicknameError

instance inputFieldErrorWalletNicknameError :: InputFieldError WalletNicknameError where
  inputErrorToString EmptyWalletNickname = "Nickname cannot be blank"
  inputErrorToString DuplicateWalletNickname = "Nickname is already in use in your contacts"
  inputErrorToString BadWalletNickname = "Nicknames can only contain letters and numbers"

data WalletIdError
  = EmptyWalletId
  | DuplicateWalletId
  | InvalidWalletId
  | UnconfirmedWalletId
  | NonexistentWalletId

derive instance eqWalletIdError :: Eq WalletIdError

instance inputeFieldErrorWalletIdError :: InputFieldError WalletIdError where
  inputErrorToString EmptyWalletId = "Wallet ID cannot be blank"
  inputErrorToString DuplicateWalletId = "Wallet ID is already in your contacts"
  inputErrorToString InvalidWalletId = "Wallet ID is not valid"
  inputErrorToString UnconfirmedWalletId = "Looking up wallet..."
  inputErrorToString NonexistentWalletId = "Wallet not found"

data Action
  = CloseWalletDataCard
  | SetCardSection CardSection
  | SaveWallet (Maybe String)
  | CancelNewContactForRole
  | WalletNicknameInputAction (InputField.Action WalletNicknameError)
  | WalletIdInputAction (InputField.Action WalletIdError)
  | SetRemoteWalletInfo (WebData WalletInfo)
  | UseWallet WalletNickname PlutusAppId
  | ClipboardAction Clipboard.Action

instance actionIsEvent :: IsEvent Action where
  toEvent CloseWalletDataCard = Just $ defaultEvent "CloseWalletDataCard"
  toEvent (SetCardSection _) = Just $ defaultEvent "SetCardSection"
  toEvent (SaveWallet _) = Just $ defaultEvent "SaveWallet"
  toEvent CancelNewContactForRole = Nothing
  toEvent (WalletNicknameInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (WalletIdInputAction inputFieldAction) = toEvent inputFieldAction
  toEvent (SetRemoteWalletInfo _) = Nothing
  toEvent (UseWallet _ _) = Just $ defaultEvent "UseWallet"
  toEvent (ClipboardAction _) = Just $ defaultEvent "ClipboardAction"
