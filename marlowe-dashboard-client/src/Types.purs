module Types
  ( WebData
  , ContractInstanceId(..)
  , contractInstanceIdFromString
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
