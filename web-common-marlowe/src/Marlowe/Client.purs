module Marlowe.Client where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Tuple (Tuple)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Input, MarloweData, MarloweParams, Slot, TransactionError, TransactionInput)
import Plutus.Contract.StateMachine (InvalidTransition, SMContractError)
import Wallet.Types (ContractError)

type MarloweSlotRange
  = Tuple Slot Slot

type MarloweInput
  = Tuple MarloweSlotRange (Array Input)

data MarloweError
  = StateMachineError SMContractError
  | TransitionError (InvalidTransition MarloweData MarloweInput)
  | MarloweEvaluationError TransactionError
  | OtherContractError ContractError
  | RolesCurrencyError ContractError

derive instance eqMarloweError :: Eq MarloweError

derive instance genericMarloweError :: Generic MarloweError _

instance encodeMarloweError :: Encode MarloweError where
  encode a = genericEncode defaultOptions a

instance decodeMarloweError :: Decode MarloweError where
  decode a = genericDecode defaultOptions a

newtype ContractHistory
  = ContractHistory
  { chParams :: Maybe (Tuple MarloweParams MarloweData)
  , chHistory :: Array TransactionInput
  }

derive instance newtypeContractHistory :: Newtype ContractHistory _

derive instance eqContractHistory :: Eq ContractHistory

derive instance genericContractHistory :: Generic ContractHistory _

instance encodeContractHistory :: Encode ContractHistory where
  encode a = genericEncode defaultOptions a

instance decodeContractHistory :: Decode ContractHistory where
  decode a = genericDecode defaultOptions a
