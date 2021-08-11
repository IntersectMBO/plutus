module Marlowe.Client where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Input, MarloweData, MarloweParams, Slot, TransactionError, TransactionInput)
import Plutus.Contract.StateMachine (InvalidTransition, SMContractError)
import Wallet.Types (ContractError)

-- This is the state of the main marlowe (control) contract. Its purpose is to provide feedback if
-- anything goes wrong when we try to create a contract or apply inputs.
data LastResult
  = OK
  | SomeError MarloweError
  | Unknown

derive instance genericLastResult :: Generic LastResult _

instance encodeLastResult :: Encode LastResult where
  encode a = genericEncode defaultOptions a

instance decodeLastResult :: Decode LastResult where
  decode a = genericDecode defaultOptions a

data MarloweError
  = StateMachineError SMContractError
  -- ^ can arise when applying inputs if:
  --     (a) there's a duplicate marlowe contract (which could theoretially happen if someone is deliberately trying to break things)
  --     (b) the contract doesn't exist or has already closed
  --     (c) you don't have enough money
  | TransitionError (InvalidTransition MarloweData MarloweInput)
  -- ^ can arise when applying inputs if:
  --     (a) you don't have the right role token (the frontend should rule this out anyway)
  --     (b) someone else made the move first
  --     (c) you don't have enough money
  | MarloweEvaluationError TransactionError
  -- ^ can arise when applying inputs (should just match the frontend semantics)
  | OtherContractError ContractError
  -- ^ can arise when creating a contract if you don't provide pubKeys for all the roles (the frontend should rule this out anyway)
  -- note `ContractError` is more general, but we only use this here for its `OtherError` constructor, and in this one specific case
  | RolesCurrencyError ContractError

-- ^ can arise when creating a contract if you don't have enough money
derive instance eqMarloweError :: Eq MarloweError

derive instance genericMarloweError :: Generic MarloweError _

instance encodeMarloweError :: Encode MarloweError where
  encode a = genericEncode defaultOptions a

instance decodeMarloweError :: Decode MarloweError where
  decode a = genericDecode defaultOptions a

type MarloweInput
  = Tuple MarloweSlotRange (Array Input)

type MarloweSlotRange
  = Tuple Slot Slot

-- This is the state of the follower contract. Its purpose is to provide us with an up-to-date
-- transaction history for a Marlowe contract running on the blockchain.
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

_chParams :: Lens' ContractHistory (Maybe (Tuple MarloweParams MarloweData))
_chParams = _Newtype <<< prop (SProxy :: SProxy "chParams")

_chHistory :: Lens' ContractHistory (Array TransactionInput)
_chHistory = _Newtype <<< prop (SProxy :: SProxy "chHistory")
