{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Plutus.Contract.State(
    -- * Contract state
    -- $contractstate
    Contract
    , State(..)
    , ContractRequest(..)
    , ContractResponse(..)
    , mapE
    , mapW
    , insertAndUpdateContract
    , initialiseContract
    , mkResponse
    ) where

import           Control.Monad.Freer.Extras.Log   (LogMessage)
import           Data.Aeson                       (FromJSON, ToJSON, Value)
import           Data.Bifunctor                   (Bifunctor (..))
import           Data.Foldable                    (toList)
import           GHC.Generics                     (Generic)

import           Data.Text.Prettyprint.Doc.Extras (Pretty, PrettyShow (..))
import           Plutus.Contract.Checkpoint       (CheckpointKey, CheckpointStore)
import           Plutus.Contract.Resumable
import           Plutus.Contract.Schema           (Event (..), Handlers (..))
import           Plutus.Contract.Types            hiding (lastLogs, logs, observableState)

-- $contractstate
-- Types for initialising and running instances of 'Contract's. The types and
-- functions in this module are convenient wrappers around types and functions
-- from 'Plutus.Contract.Types', exposing an interface that is suitable
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
data State w e = State
    { record          :: Responses e
    , checkpoints     :: CheckpointStore
    , observableState :: w
    }
    deriving stock (Generic, Eq, Show, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)

instance Bifunctor State where
    bimap f g s =
        s{record = fmap g (record s), observableState = f (observableState s)}

-- | A request sent to a contract instance. It contains the previous 'State' of
--   the instance, and a 'Response' to one of the requests of the instance.
data ContractRequest w s = ContractRequest
    { oldState :: State w (CheckpointKey, s)
    , event    :: Response s
    }
    deriving stock (Generic, Eq, Show, Functor, Foldable, Traversable)
    deriving anyclass (ToJSON, FromJSON)
    deriving Pretty via PrettyShow (ContractRequest w s)

-- | A response produced by a contract instance. It contains the new 'State',
--   the list of endpoints that can be called, logs produced by the contract,
--   possibly an error message, and the accumulated observable state.
data ContractResponse w e s h = ContractResponse
    { newState  :: State w (CheckpointKey, s) -- ^ Serialised state of the contract (internal)
    , hooks     :: [Request h] -- ^ Open requests that can be handled
    , logs      :: [LogMessage Value] -- ^ Logs produced by the contract
    , lastLogs  :: [LogMessage Value] -- ^ Logs produced in the last step
    , err       :: Maybe e -- ^ Error that happened during contract execution
    , lastState :: w -- ^ Observable state produced in the last step
    }
    deriving stock (Generic, Eq, Show, Functor)
    deriving anyclass (ToJSON, FromJSON)

instance Bifunctor (ContractResponse w e) where
    bimap f g c@ContractResponse{newState} =
        fmap g c{ newState = fmap (fmap f) newState }

mapE :: forall e f w s h. (e -> f) -> ContractResponse w e s h -> ContractResponse w f s h
mapE f c@ContractResponse{err} = c{err = fmap f err}

mapW :: forall w q e s h. (w -> q) -> ContractResponse w e s h -> ContractResponse q e s h
mapW f c@ContractResponse{lastState, newState} = c{lastState = f lastState, newState = first f newState}

-- | Run one step of the contract by restoring it to its previous state and
--   feeding it a single new 'Response' event.
insertAndUpdateContract ::
    forall w s e a.
    (Monoid w, ToJSON w, FromJSON w)
    => Contract w s e a -- ^ The 'Contract' with schema @s@ error type @e@.
    -> ContractRequest w (Event s) -- ^  The 'ContractRequest' value with the previous state and the new event.
    -> ContractResponse w e (Event s) (Handlers s)
insertAndUpdateContract (Contract con) ContractRequest{oldState=State record checkpoints oldW, event} =
    mkResponse
        oldW
        $ shrinkResumableResult
        $ insertAndUpdate con checkpoints record event

mkResponse :: forall w e s h a.
    Monoid w
    => w
    -> ResumableResult w e s h a
    -> ContractResponse w e s h
mkResponse oldW ResumableResult{_responses, _requests=Requests{unRequests},_checkpointStore, _logs, _lastLogs, _finalState, _lastState=lastState} =
    ContractResponse
        { hooks = unRequests
        , newState = State { record = _responses, checkpoints=_checkpointStore, observableState = oldW <> lastState }
        , logs = toList _logs
        , lastLogs = toList _lastLogs
        , err = either Just (const Nothing) _finalState
        , lastState
        }

-- | The 'ContractResponse' with the initial state of the contract.
initialiseContract ::
    forall w s e a.
    (Monoid w, ToJSON w, FromJSON w)
    => Contract w s e a
    -> ContractResponse w e (Event s) (Handlers s)
initialiseContract (Contract c) = mkResponse mempty $ runResumable [] mempty c
