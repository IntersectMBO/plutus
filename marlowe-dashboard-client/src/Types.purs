module Types
  ( WebData
  , DecodedWebData
  , ContractInstanceId(..)
  , MarloweParams
  , ValidatorHash
  , MarloweData
  ) where

-- this module is for miscellaneous types that don't belong anywhere else
-- (or would lead to cyclic dependencies if put somewhere they might more naturall belong)
import Prelude
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.List.NonEmpty (NonEmptyList)
import Data.Newtype (class Newtype)
import Data.UUID (UUID)
import Foreign (ForeignError)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Contract, CurrencySymbol, State)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type WebData
  = RemoteData AjaxError

type DecodedWebData
  = RemoteData (Either AjaxError (NonEmptyList ForeignError))

newtype ContractInstanceId
  = ContractInstanceId UUID

derive instance newtypeContractInstanceId :: Newtype ContractInstanceId _

derive instance eqContractInstanceId :: Eq ContractInstanceId

derive instance genericContractInstanceId :: Generic ContractInstanceId _

instance encodeContractInstanceId :: Encode ContractInstanceId where
  encode value = genericEncode defaultOptions value

instance decodeContractInstanceId :: Decode ContractInstanceId where
  decode value = genericDecode defaultOptions value

-- FIXME: check serialization of this type works with the backend
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

-- FIXME: check serialization of this type works with the backend
type ValidatorHash
  = String

-- note: the wallet companion contract state has type `Map MarloweParams MarloweData`
newtype MarloweData
  = MarloweData
  { marloweContract :: Contract
  , marloweState :: State
  }

derive instance newtypeMarloweData :: Newtype MarloweData _

derive instance eqMarloweData :: Eq MarloweData

derive instance genericMarloweData :: Generic MarloweData _

instance encodeMarloweData :: Encode MarloweData where
  encode value = genericEncode defaultOptions value

instance decodeMarloweData :: Decode MarloweData where
  decode value = genericDecode defaultOptions value
