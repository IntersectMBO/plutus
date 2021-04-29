module Marlowe.PAB
  ( ContractType(..)
  , contractExe
  , contractType
  , transactionFee
  , contractCreationFee
  , ContractInstanceId(..)
  , MarloweParams(..)
  , ValidatorHash
  , MarloweData(..)
  , History(..)
  ) where

import Prelude
import Data.BigInteger (BigInteger, fromInt)
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

-- in the PAB, transactions have a fixed cost of 10 lovelace; in the real node,
-- transaction fees will vary, but this may still serve as a good approximation
transactionFee :: BigInteger
transactionFee = fromInt 10

-- FIXME: it appears that creating a contract currently requires three transactions,
-- but I believe it should be possible with one; check this with Alex
contractCreationFee :: BigInteger
contractCreationFee = transactionFee * (fromInt 3)

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

-- `MarloweParams` are used to identify a Marlowe contract in the PAB, and the wallet
-- companion contract state is a `Map MarloweParams MarloweData`. We are not currently
-- generating PureScript types to match the Haskell `MarloweParams` and `MarloweData`
-- types (side note: perhaps we should be). We have a `CurrencySymbol` type in
-- `Marlowe.Semantics`, but it is just an alias for String. We could use that here for
-- the `rolesCurrency` value, and convert using its Bridge instance when sharing data
-- with the PAB. However, we currently don't need to do anything with `MarloweParams` on
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

-- This is the observable state of the `FollowerContract`. The `MarloweParams` identify the
-- the Marlowe contract on the blockchain, the `MarloweData` represents the initial contract
-- and state, and the array of `TransactionInput` records all the transactions of the
-- contract so far.
newtype History
  = History (Tuple3 MarloweParams MarloweData (Array TransactionInput))

derive instance newtypeHistory :: Newtype History _

derive instance genericHistory :: Generic History _

instance encodeHistory :: Encode History where
  encode value = genericEncode defaultOptions value

instance decodeHistory :: Decode History where
  decode value = genericDecode defaultOptions value
