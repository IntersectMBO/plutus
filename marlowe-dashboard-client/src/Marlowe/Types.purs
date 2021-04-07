module Marlowe.Types
  ( ContractInstanceId(..)
  , contractInstanceIdFromString
  , ContractInstanceClientState(..)
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.UUID (UUID, parseUUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint)
import Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)

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

newtype ContractInstanceClientState
  = ContractInstanceClientState
  { cicContract :: ContractInstanceId
  , cicContractState :: PartiallyDecodedResponse ActiveEndpoint
  }
