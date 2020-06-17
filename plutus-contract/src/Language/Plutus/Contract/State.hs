{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Plutus.Contract.State(
    -- * Contract state
    -- $contractstate
    Contract
    , State(..)
    , ContractRequest(..)
    , ContractResponse(..)
    , insertAndUpdateContract
    , initialiseContract
    ) where

import           Data.Aeson                          (FromJSON, ToJSON)
import           GHC.Generics                        (Generic)

import           Data.Text.Prettyprint.Doc.Extras    (Pretty, PrettyShow (..))
import           Language.Plutus.Contract.Checkpoint (CheckpointStore)
import           Language.Plutus.Contract.Resumable
import           Language.Plutus.Contract.Schema     (Event (..), Handlers (..))
import           Language.Plutus.Contract.Types

-- $contractstate
-- Types for initialising and running instances of 'Contract's. The types and
-- functions in this module are convenient wrappers around types and functions
-- from 'Language.Plutus.Contract.Types', exposing an interface that is suitable
-- for consumption by the SCB. In particular this means that
-- 'insertAndUpdateContract' has a single argument, and its argument & return
-- types can be serialised to JSON easily.
--
-- To actually run a contract, follow this workflow:
--
-- 1. Call 'initialiseContract' to get the initial 'ContractResponse'.
-- 2. Look at the 'hooks' of this value and generate an answer to one of them.
--    This answer is a 'Response' @s@ value.
-- 3. Call 'insertAndUpdateContract' with a 'ContractRequest' whose 'oldState'
--    field has the value of 'newState' of the previous response, and whose
--    'event' is the next answer (step 2).
-- 4. Take the new 'ContractResponse' and go back to step 2, until you get a
--    response with no requests, or an error.

-- | The state of a 'Contract', containing all responses that have been fed to
--   it, and checkpoints that it produced.
data State e = State
    { record      :: Responses e
    , checkpoints :: CheckpointStore
    }
    deriving stock (Generic, Eq, Show, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)

-- | A request sent to a contract instance. It contains the previous 'State' of
--   the instance, and a 'Response' to one of the requests of the instance.
data ContractRequest s = ContractRequest
    { oldState :: State s
    , event    :: Response s
    }
    deriving stock (Generic, Eq, Show, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)
    deriving Pretty via PrettyShow (ContractRequest s)

-- | A response produced by a contract instance. It contains the new 'State',
--   and the list of endpoints that can be called.
data ContractResponse s h = ContractResponse
    { newState :: State s
    , hooks    :: [Request h]
    }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | Run one step of the contract by restoring it to its previous state and
--   feeding it a single new 'Response' event.
insertAndUpdateContract ::
    forall s e a.
    Contract s e a -- ^ The 'Contract' with schema @s@ error type @e@.
    -> ContractRequest (Event s) -- ^  The 'ContractRequest' value with the previous state and the new event.
    -> Either e (ContractResponse (Event s) (Handlers s))
insertAndUpdateContract (Contract con) ContractRequest{oldState=State record checkpoints, event} =
    mkResponse <$> insertAndUpdate con checkpoints record event

mkResponse :: forall s e a. ResumableResult s e a -> ContractResponse s e
mkResponse ResumableResult{wcsResponses, wcsRequests=Requests{unRequests},wcsCheckpointStore} =
    ContractResponse{hooks = unRequests, newState = State { record = wcsResponses, checkpoints=wcsCheckpointStore } }

-- | The 'ContractResponse' with the initial state of the contract.
initialiseContract
    :: forall s e a.
    Contract s e a
    -> Either e (ContractResponse (Event s) (Handlers s))
initialiseContract (Contract c) = mkResponse <$> runResumable [] mempty c
