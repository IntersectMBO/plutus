module Types
  ( WebData
  , ContractInstanceId(..)
  , contractInstanceIdFromString
  , MarloweParams
  , ValidatorHash
  ) where

-- this module is for miscellaneous types that don't belong anywhere else
-- (or would lead to cyclic dependencies if put somewhere they might more naturall belong)
import Prelude
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.UUID (UUID, parseUUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (CurrencySymbol)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type WebData
  = RemoteData AjaxError

newtype ContractInstanceId
  = ContractInstanceId UUID

derive instance newtypeContractInstanceId :: Newtype ContractInstanceId _

derive instance eqContractInstanceId :: Eq ContractInstanceId

derive instance genericContractInstanceId :: Generic ContractInstanceId _

instance encodeContractInstanceId :: Encode ContractInstanceId where
  encode value = genericEncode defaultOptions value

instance decodeContractInstanceId :: Decode ContractInstanceId where
  decode value = genericDecode defaultOptions value

contractInstanceIdFromString :: String -> Maybe ContractInstanceId
contractInstanceIdFromString contractInstanceIdString = case parseUUID contractInstanceIdString of
  Just uuid -> Just $ ContractInstanceId uuid
  _ -> Nothing

-- TODO: check serialization of this type works with the backend
newtype MarloweParams
  = MarloweParams
  { rolePayoutValidatorHash :: ValidatorHash
  , rolesCurrency :: CurrencySymbol
  }

derive instance newtypeMarloweParams :: Newtype MarloweParams _

derive instance eqMarloweParams :: Eq MarloweParams

derive instance genericMarloweParams :: Generic MarloweParams _

instance encodeMarloweParams :: Encode MarloweParams where
  encode value = genericEncode defaultOptions value

instance decodeMarloweParams :: Decode MarloweParams where
  decode value = genericDecode defaultOptions value

-- TODO: check serialization of this type works with the backend
type ValidatorHash
  = String
