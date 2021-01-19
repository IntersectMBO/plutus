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

import           Control.Monad.Freer.Log             (LogMessage)
import           Data.Aeson                          (FromJSON, ToJSON, Value)
import           Data.Foldable                       (toList)
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
-- for consumption by the PAB. In particular this means that
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
--   the list of endpoints that can be called, logs produced by the contract,
--   and possibly an error
data ContractResponse e s h = ContractResponse
    { newState :: State s
    , hooks    :: [Request h]
    , logs     :: [LogMessage Value]
    , err      :: Maybe e
    }
    deriving stock (Generic, Eq, Show)
    deriving anyclass (ToJSON, FromJSON)

-- | Run one step of the contract by restoring it to its previous state and
--   feeding it a single new 'Response' event.
insertAndUpdateContract ::
    forall s e a.
    Contract s e a -- ^ The 'Contract' with schema @s@ error type @e@.
    -> ContractRequest (Event s) -- ^  The 'ContractRequest' value with the previous state and the new event.
    -> ContractResponse e (Event s) (Handlers s)
insertAndUpdateContract (Contract con) ContractRequest{oldState=State record checkpoints, event} =
    mkResponse $ insertAndUpdate con checkpoints record event

mkResponse :: forall e s h a.
    ResumableResult e s h a
    -> ContractResponse e s h
mkResponse ResumableResult{wcsResponses, wcsRequests=Requests{unRequests},wcsCheckpointStore, wcsLogs, wcsFinalState} =
    ContractResponse
        { hooks = unRequests
        , newState = State { record = wcsResponses, checkpoints=wcsCheckpointStore }
        , logs = toList wcsLogs
        , err = either Just (const Nothing) wcsFinalState
        }

-- | The 'ContractResponse' with the initial state of the contract.
initialiseContract
    :: forall s e a.
    Contract s e a
    -> ContractResponse e (Event s) (Handlers s)
initialiseContract (Contract c) = mkResponse $ runResumable [] mempty c
