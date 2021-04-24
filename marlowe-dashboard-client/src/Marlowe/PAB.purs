module Marlowe.PAB
  ( ContractType(..)
  , contractExe
  , contractType
  , ContractInstanceId(..)
  , MarloweParams(..)
  , ValidatorHash
  , MarloweData(..)
  , History
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple3)
import Data.UUID (UUID)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Contract, State, TransactionInput)
import Plutus.PAB.Effects.Contract.ContractExe (ContractExe(..))
import Plutus.V1.Ledger.Value (CurrencySymbol)

foreign import marloweContractPath_ :: String

foreign import walletCompanionContractPath_ :: String

foreign import walletFollowerContractPath_ :: String

data ContractType
  = MarloweContract
  | WalletCompanionContract
  | WalletFollowerContract

contractExe :: ContractType -> ContractExe
contractExe MarloweContract = ContractExe { contractPath: marloweContractPath_ }

contractExe WalletCompanionContract = ContractExe { contractPath: walletCompanionContractPath_ }

contractExe WalletFollowerContract = ContractExe { contractPath: walletFollowerContractPath_ }

contractType :: ContractExe -> Maybe ContractType
contractType exe
  | exe == contractExe MarloweContract = Just MarloweContract

contractType exe
  | exe == contractExe WalletCompanionContract = Just WalletCompanionContract

contractType exe
  | exe == contractExe WalletFollowerContract = Just WalletFollowerContract

contractType _ = Nothing

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

newtype History
  = History (Tuple3 MarloweParams MarloweData (Array TransactionInput))

derive instance newtypeHistoryId :: Newtype History _

derive instance genericHistoryId :: Generic History _

instance encodeHistoryId :: Encode History where
  encode value = genericEncode defaultOptions value

instance decodeHistoryId :: Decode History where
  decode value = genericDecode defaultOptions value
