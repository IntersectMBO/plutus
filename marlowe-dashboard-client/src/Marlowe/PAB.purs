module Marlowe.PAB
  ( ContractInstanceId(..)
  , MarloweParams(..)
  , ValidatorHash
  , MarloweData(..)
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.UUID (UUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Contract, State)
import Plutus.V1.Ledger.Value (CurrencySymbol)

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

-- MarloweParams are used to identify a Marlowe contract in the PAB, and the wallet
-- companion contract state is a Map MarloweParams MarloweData. We are not currently
-- generating PureScript types to match the Haskell MarloweParams and MarloweData
-- types (side note: perhaps we should be). We have a CurrencySymbol type in
-- Marlowe.Semantics, but it is just an alias for String. We could use that here for
-- the `rolesCurrency` value, and convert using its Bridge instance when sharing data
-- with the PAB. However, we currently don't need to do anything with MarloweParams on
-- the frontend except save them and send them back to the PAB (to join a contract that
-- is already running), so it is simpler just to use the generated type in this case.
type MarloweParams
  = { rolePayoutValidatorHash :: ValidatorHash
    , rolesCurrency :: CurrencySymbol
    }

type ValidatorHash
  = String

type MarloweData
  = { marloweContract :: Contract
    , marloweState :: State
    }
