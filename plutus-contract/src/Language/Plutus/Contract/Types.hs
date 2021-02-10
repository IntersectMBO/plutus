{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MonoLocalBinds         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
module Language.Plutus.Contract.Types(
    ContractEffs
    , handleContractEffs
    , Contract(..)
    -- * Select
    , select
    , selectEither
    -- * Error handling
    , ContractError(..)
    , AsContractError(..)
    , MatchingError(..)
    , mapError
    , throwError
    , runError
    , handleError
    -- * Checkpoints
    , AsCheckpointError(..)
    , CheckpointError(..)
    , checkpoint
    -- * Run and update
    , runResumable
    , insertAndUpdate
    , runWithRecord
    -- * State
    , ResumableResult(..)
    , responses
    , requests
    , finalState
    , logs
    , checkpointStore
    -- * Run with continuations
    , SuspendedContract(..)
    , resumableResult
    , continuations
    , checkpointKey
    , suspend
    , runStep
    ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Except                (MonadError (..))
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Control.Monad.Freer.Error           (Error)
import qualified Control.Monad.Freer.Error           as E
import           Control.Monad.Freer.Extras          (raiseEnd4, raiseUnderN)
import           Control.Monad.Freer.Log             (LogMessage, LogMsg, handleLogIgnore, handleLogWriter)
import           Control.Monad.Freer.NonDet
import           Control.Monad.Freer.State
import qualified Control.Monad.Freer.Writer          as W
import           Data.Aeson                          (Value)
import qualified Data.Aeson                          as Aeson
import           Data.Foldable                       (foldl')
import           Data.Maybe                          (fromMaybe)
import           Data.Sequence                       (Seq)
import           Data.Void                           (Void)
import           GHC.Generics                        (Generic)

import           Language.Plutus.Contract.Schema     (Event (..), Handlers (..))

import           Language.Plutus.Contract.Checkpoint (AsCheckpointError (..), Checkpoint (..), CheckpointError (..),
                                                      CheckpointKey, CheckpointLogMsg, CheckpointStore,
                                                      handleCheckpoint, jsonCheckpoint)
import           Language.Plutus.Contract.Resumable  hiding (responses, select)
import qualified Language.Plutus.Contract.Resumable  as Resumable

import qualified Language.PlutusTx.Applicative       as PlutusTx
import qualified Language.PlutusTx.Functor           as PlutusTx
import           Prelude                             as Haskell
import           Wallet.Types                        (AsContractError (..), ContractError (..), MatchingError (..))

-- | Effects that are available to contracts.
type ContractEffs s e =
    '[ Error e
    ,  LogMsg Value
    ,  Checkpoint
    ,  Resumable (Event s) (Handlers s)
    ]

type ContractEnv = (IterationID, RequestID)

handleContractEffs ::
  forall s e effs a.
  ( Member (Error e) effs
  , Member (State CheckpointStore) effs
  , Member (State CheckpointKey) effs
  , Member (LogMsg CheckpointLogMsg) effs
  , Member (LogMsg Value) effs
  )
  => Eff (ContractEffs s e) a
  -> Eff effs (Maybe (MultiRequestContStatus (Event s) (Handlers s) effs a))
handleContractEffs =
  suspendNonDet @(Event s) @(Handlers s) @a @effs
  . handleResumable @(Event s) @(Handlers s)
  . handleCheckpoint
  . addEnvToCheckpoint
  . subsume @(LogMsg Value)
  . subsume @(Error e)
  . raiseEnd4
      @(Yield (Handlers s) (Event s)
        ': State IterationID
        ': NonDet
        ': State RequestID
        ': State (ReqMap (Event s) (Handlers s) effs a)
        ': State (Requests (Handlers s))
        ': effs
        )

getContractEnv ::
  forall effs.
  ( Member (State RequestID) effs
  , Member (State IterationID) effs
  )
  => Eff effs ContractEnv
getContractEnv = (,) <$> get <*> get

putContractEnv ::
  forall effs.
  ( Member (State RequestID) effs
  , Member (State IterationID) effs
  )
  => ContractEnv
  -> Eff effs ()
putContractEnv (it, req) = put it >> put req

addEnvToCheckpoint ::
  forall effs.
  ( Member (State RequestID) effs
  , Member (State IterationID) effs
  )
  => Eff (Checkpoint ': effs)
  ~> Eff (Checkpoint ': effs)
addEnvToCheckpoint = reinterpret @Checkpoint @Checkpoint @effs $ \case
  DoCheckpoint -> send DoCheckpoint
  AllocateKey -> send AllocateKey
  Store k k' a -> do
    env <- getContractEnv
    send $ Store k k' (env, a)
  Retrieve k -> do
    result <- send $ Retrieve @(ContractEnv, _) k
    case result of
      Right (Just (env, a)) -> do
        putContractEnv env
        pure (Right (Just a))
      Left err -> pure (Left err)
      Right Nothing -> pure (Right Nothing)

-- | @Contract s a@ is a contract with schema 's', producing a value of
--  type 'a' or a 'ContractError'. See note [Contract Schema].
--
newtype Contract s e a = Contract { unContract :: Eff (ContractEffs s e) a }
  deriving newtype (Functor, Applicative, Monad)

instance MonadError e (Contract s e) where
    throwError = Contract . E.throwError
    catchError (Contract f) handler =
      Contract
      $ E.catchError f
      $ unContract . handler

instance PlutusTx.Functor (Contract s e) where
  fmap = Haskell.fmap

instance PlutusTx.Applicative (Contract s e) where
  (<*>) = (Haskell.<*>)
  pure  = Haskell.pure

instance Bifunctor (Contract s) where
  bimap l r = mapError l . fmap r

-- | @select@ returns the contract that makes progress first, discarding the
--   other one.
select :: forall s e a. Contract s e a -> Contract s e a -> Contract s e a
select (Contract l) (Contract r) = Contract (Resumable.select @(Event s) @(Handlers s) @(ContractEffs s e) l r)

-- | A variant of @select@ for contracts with different return types.
selectEither :: forall s e a b. Contract s e a -> Contract s e b -> Contract s e (Either a b)
selectEither l r = (Left <$> l) `select` (Right <$> r)

-- | Write the current state of the contract to a checkpoint.
checkpoint :: forall s e a. (AsCheckpointError e, Aeson.FromJSON a, Aeson.ToJSON a) => Contract s e a -> Contract s e a
checkpoint = Contract . jsonCheckpoint @e . unContract

-- | Transform any exceptions thrown by the 'Contract' using the given function.
mapError ::
  forall s e e' a.
  (e -> e')
  -> Contract s e a
  -> Contract s e' a
mapError f = handleError (throwError . f)

-- | Turn a contract with error type 'e' and return type 'a' into one with
--   error type 'Void' (ie. throwing no errors) that returns 'Either e a'
runError ::
  forall s e a.
  Contract s e a
  -> Contract s Void (Either e a)
runError (Contract r) = Contract (E.runError $ raiseUnderN @'[E.Error Void] r)

-- | Handle errors, potentially throwing new errors.
handleError ::
  forall s e e' a.
  (e -> Contract s e' a)
  -> Contract s e a
  -> Contract s e' a
handleError f (Contract c) = Contract c' where
  c' = E.handleError @e (raiseUnderN @'[E.Error e'] c) (fmap unContract f)

type SuspendedContractEffects e i =
  Error e
  ': State CheckpointKey
  ': State CheckpointStore
  ': LogMsg CheckpointLogMsg
  ': LogMsg Value
  ': W.Writer (Seq (LogMessage Value))
  ': '[]

-- | The result of running a 'Resumable'
data ResumableResult e i o a =
    ResumableResult
        { _responses       :: Responses i -- The record with the resumable's execution history
        , _requests        :: Requests o -- Handlers that the 'Resumable' has registered
        , _finalState      :: Either e (Maybe a) -- Error or final state of the 'Resumable' (if it has finished)
        , _logs            :: Seq (LogMessage Value) -- Log messages
        , _checkpointStore :: CheckpointStore
        }
        deriving stock Generic
        deriving anyclass (Aeson.ToJSON, Aeson.FromJSON)

makeLenses ''ResumableResult

data SuspendedContract e i o a =
  SuspendedContract
    { _resumableResult :: ResumableResult e i o a
    , _continuations   :: Maybe (MultiRequestContStatus i o (SuspendedContractEffects e i) a)
    , _checkpointKey   :: CheckpointKey
    }

makeLenses ''SuspendedContract

runResumable ::
  [Response (Event s)]
  -> CheckpointStore
  -> Eff (ContractEffs s e) a
  -> ResumableResult e (Event s) (Handlers s) a
runResumable events store action =
  let initial = suspend action & resumableResult . checkpointStore .~ store
      runStep' con rsp = fromMaybe con (runStep con rsp)
  in foldl' runStep' initial events & view resumableResult

runWithRecord ::
  forall s e a.
  Eff (ContractEffs s e) a
  -> CheckpointStore
  -> Responses (Event s)
  -> ResumableResult e (Event s) (Handlers s) a
runWithRecord action store events =
  runResumable (Resumable.responses events) store action

mkResult ::
  forall s e a.
  (((Either e (Maybe (MultiRequestContStatus (Event s) (Handlers s) (SuspendedContractEffects e (Event s)) a)), CheckpointKey), CheckpointStore), Seq (LogMessage Value))
  -> SuspendedContract e (Event s) (Handlers s) a
mkResult (((initialRes, cpKey), cpStore), newLogs) =
  SuspendedContract
      { _resumableResult =
          ResumableResult
            { _responses = mempty
            , _requests =
                let getRequests = \case { AContinuation (MultiRequestContinuation{ndcRequests}) -> Just ndcRequests; _ -> Nothing }
                in either mempty (fromMaybe mempty) $ fmap (>>= getRequests) initialRes
            , _finalState =
                let getResult = \case { AResult a -> Just a; _ -> Nothing } in
                fmap (>>= getResult) initialRes
            , _logs = newLogs
            , _checkpointStore = cpStore
            }
      , _continuations = either (const Nothing) id initialRes
      , _checkpointKey = cpKey
      }

runSuspContractEffects ::
  forall e i a.
  CheckpointKey
  -> CheckpointStore
  -> Eff (SuspendedContractEffects e i) a
  -> (((Either e a, CheckpointKey), CheckpointStore), Seq (LogMessage Value))
runSuspContractEffects cpKey cpStore =
  run
    . W.runWriter @(Seq (LogMessage Value))
    . interpret (handleLogWriter @Value @(Seq (LogMessage Value)) $ unto return)
    . handleLogIgnore @CheckpointLogMsg
    . runState cpStore
    . runState cpKey
    . E.runError @e

-- | Run an action of @ContractEffs@ until it requests input for the first
--   time, returning the 'SuspendedContract'
suspend ::
  forall s e a.
  Eff (ContractEffs s e) a -- ^ The contract
  -> SuspendedContract e (Event s) (Handlers s) a
suspend action =
  mkResult
    $ runSuspContractEffects
      (0 :: CheckpointKey)
      (mempty @CheckpointStore)
      (handleContractEffs @_ @_ @(SuspendedContractEffects e (Event s)) action)

-- | Feed a 'Response' to a 'SuspendedContract'.
runStep ::
  forall s e a.
  SuspendedContract e (Event s) (Handlers s) a
  -> Response (Event s)
  -> Maybe (SuspendedContract e (Event s) (Handlers s) a)
runStep SuspendedContract{_continuations=Just (AContinuation MultiRequestContinuation{ndcCont}), _checkpointKey, _resumableResult=ResumableResult{_responses, _checkpointStore}} event =
  Just
    $ set (resumableResult . responses) (insertResponse event _responses)
    $ mkResult
    $ runSuspContractEffects
        _checkpointKey
        _checkpointStore
        $ ndcCont event
runStep _ _ = Nothing

insertAndUpdate ::
  forall s e a.
  Eff (ContractEffs s e) a
  -> CheckpointStore
  -> Responses (Event s)
  -> Response (Event s)
  -> ResumableResult e (Event s) (Handlers s) a
insertAndUpdate action store record newResponse =
  runWithRecord action store (insertResponse newResponse record)
