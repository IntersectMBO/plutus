module Types
  ( AjaxResponse
  , DecodedAjaxResponse
  , WebData
  , DecodedWebData
  , ContractInstanceId(..)
  ) where

import Prelude
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.List.NonEmpty (NonEmptyList)
import Data.Newtype (class Newtype)
import Data.UUID (UUID)
import Foreign (ForeignError)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Network.RemoteData (RemoteData)
import Servant.PureScript.Ajax (AjaxError)

type AjaxResponse
  = Either AjaxError

type DecodedAjaxResponse
  = Either (Either AjaxError (NonEmptyList ForeignError))

type WebData
  = RemoteData AjaxError

type DecodedWebData
  = RemoteData (Either AjaxError (NonEmptyList ForeignError))

-- TODO: I want to put this in Contract.Types, but then there's a cyclic dependency
-- between Contract.Types and WalletData.Types. There might be a better organisation
-- of the types that avoids this problem.
newtype ContractInstanceId
  = ContractInstanceId UUID

derive instance newtypeContractInstanceId :: Newtype ContractInstanceId _

derive instance eqContractInstanceId :: Eq ContractInstanceId

derive instance ordContractInstanceId :: Ord ContractInstanceId

derive instance genericContractInstanceId :: Generic ContractInstanceId _

instance encodeContractInstanceId :: Encode ContractInstanceId where
  encode value = genericEncode defaultOptions value

instance decodeContractInstanceId :: Decode ContractInstanceId where
  decode value = genericDecode defaultOptions value
