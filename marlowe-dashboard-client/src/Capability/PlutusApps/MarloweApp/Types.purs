-- The types are defined separated from the MarloweApp to avoid this circular dependency
-- Capability.PlutusApps.MarloweApp -> AppM -> Env -> Capability.PlutusApps.MarloweApp
module Capability.PlutusApps.MarloweApp.Types
  ( LastResult(..)
  , EndpointName
  , MarloweError
  , MarloweAppState
  , EndpointMutex
  , MarloweAppEndpointMutexEnv
  ) where

import Prologue
import Data.Generic.Rep (class Generic)
import Data.UUID (UUID)
import Data.Tuple.Nested (type (/\))
import Effect.AVar (AVar)
import Foreign.Class (class Encode, class Decode)
import Foreign.Generic (defaultOptions, genericDecode, genericEncode)
import Marlowe.Semantics (Input, MarloweData, Slot, TransactionError)
import Plutus.Contract.StateMachine (InvalidTransition, SMContractError)
import Wallet.Types (ContractError)

type EndpointName
  = String

-- The Plutus contract state keeps track of the result of the last action. This is needed because
-- the PAB needs to return inmediatly and the result might take a while to compute.
data LastResult
  = OK UUID EndpointName
  | SomeError UUID EndpointName MarloweError
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

-- We use an alias because we could later on add more info to the state
type MarloweAppState
  = LastResult

-- The plutus contracts can have their endpoints active or inactive. We use
-- this object with Mutex to avoid calling an inactive endpoint and to keep
-- track of the different requests.
type EndpointMutex
  = { create :: AVar Unit
    , applyInputs :: AVar Unit
    , redeem :: AVar Unit
    -- For each request we fire, we store in a queue the tuple of the
    -- request id and a mutex to wait for the response. We use an array
    -- instead of a Map because we only want to keep a limited number of
    -- requests.
    , requests :: AVar (Array (UUID /\ AVar LastResult))
    }

type MarloweAppEndpointMutexEnv env
  = { marloweAppEndpointMutex :: EndpointMutex | env }
