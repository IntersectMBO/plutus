{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
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
    -- * Checkpoints
    , AsCheckpointError(..)
    , CheckpointError(..)
    , checkpoint
    -- * Run and update
    , runResumable
    , insertAndUpdate
    , runWithRecord
    , handleContractEffs
    -- * State
    , ResumableResult(..)

    ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Except                (MonadError (..))
import           Control.Monad.Freer
import           Control.Monad.Freer.Coroutine
import           Control.Monad.Freer.Error           (Error)
import qualified Control.Monad.Freer.Error           as E
import           Control.Monad.Freer.Extras          (raiseEnd3, raiseUnderN)
import           Control.Monad.Freer.Log             (LogMsg, handleLogIgnore)
import           Control.Monad.Freer.NonDet
import           Control.Monad.Freer.Reader
import           Control.Monad.Freer.State
import qualified Data.Aeson                          as Aeson
import           Data.String                         (IsString (..))
import           Data.Text                           (Text)
import qualified Data.Text                           as T
import           Data.Text.Prettyprint.Doc           (Pretty, pretty, (<+>))

import           Language.Plutus.Contract.Schema     (Event (..), Handlers (..))

import           Language.Plutus.Contract.Checkpoint (AsCheckpointError, Checkpoint (..), CheckpointError (..),
                                                      CheckpointKey, CheckpointLogMsg, CheckpointStore,
                                                      handleCheckpoint, jsonCheckpoint)
import qualified Language.Plutus.Contract.Checkpoint as C
import           Language.Plutus.Contract.Resumable  hiding (select)
import qualified Language.Plutus.Contract.Resumable  as Resumable

import qualified Language.PlutusTx.Applicative       as PlutusTx
import qualified Language.PlutusTx.Functor           as PlutusTx
import           Ledger.Constraints.OffChain         (MkTxError)
import           Prelude                             as Haskell
import           Wallet.API                          (WalletAPIError)
import           Wallet.Emulator.Types               (AsAssertionError (..), AssertionError)

-- | An error
newtype MatchingError = WrongVariantError Text
    deriving (Eq, Ord, Show)

instance Pretty MatchingError where
  pretty = \case
    WrongVariantError t -> "Wrong variant:" <+> pretty t

data ContractError =
    WalletError WalletAPIError
    | EmulatorAssertionError AssertionError -- TODO: Why do we need this constructor
    | OtherError T.Text
    | ConstraintResolutionError MkTxError
    | ResumableError MatchingError
    | CCheckpointError CheckpointError
    deriving (Show, Eq)
makeClassyPrisms ''ContractError

instance Pretty ContractError where
  pretty = \case
    WalletError e -> "Wallet error:" <+> pretty e
    EmulatorAssertionError a -> "Emulator assertion error:" <+> pretty a
    OtherError t -> "Other error:" <+> pretty t
    ConstraintResolutionError e -> "Constraint resolution error:" <+> pretty e
    ResumableError e -> "Resumable error:" <+> pretty e
    CCheckpointError e -> "Checkpoint error:" <+> pretty e

-- | This lets people use 'T.Text' as their error type.
instance AsContractError T.Text where
    _ContractError = prism' (T.pack . show) (const Nothing)

instance IsString ContractError where
  fromString = OtherError . fromString

instance AsAssertionError ContractError where
    _AssertionError = _EmulatorAssertionError

instance AsCheckpointError ContractError where
  _CheckpointError = _CCheckpointError

-- | Effects that are available to contracts.
type ContractEffs s e =
    '[ Error e
    ,  Checkpoint
    ,  Resumable (Event s) (Handlers s)
    ]

handleContractEffs ::
  forall s e effs a.
  ( Member (Error e) effs
  , Member (Reader (Responses (Event s))) effs
  , Member (State (Requests (Handlers s))) effs
  , Member (State CheckpointStore) effs
  , Member (LogMsg CheckpointLogMsg) effs
  )
  => Eff (ContractEffs s e) a
  -> Eff effs (Maybe a)
handleContractEffs =
  evalState (0 :: CheckpointKey)
  . handleNonDetPrompt
  . handleResumable
  . handleCheckpoint
  . addEnvToCheckpoint
  . subsume @(Error e) @(Checkpoint ': Resumable (Event s) (Handlers s) ': Yield (Handlers s) (Event s) ': State IterationID ': NonDet ': State RequestID ': State CheckpointKey ': effs)
  . raiseEnd3 @(Yield (Handlers s) (Event s) ': State IterationID ': NonDet ': State RequestID ': State CheckpointKey ': effs)

type ContractEnv = (IterationID, RequestID)

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
mapError f (Contract c) = Contract c' where
  c' = E.handleError @e (raiseUnderN @'[E.Error e'] c) (E.throwError @e' . f)

runResumable ::
  [Response (Event s)]
  -> CheckpointStore
  -> Eff (ContractEffs s e) a
  -> Either e (ResumableResult (Event s) (Handlers s) a)
runResumable events store action =
  let record = foldr insertResponse mempty events in
  runWithRecord action store record

runWithRecord ::
  forall s e a.
  Eff (ContractEffs s e) a
  -> CheckpointStore
  -> Responses (Event s)
  -> Either e (ResumableResult (Event s) (Handlers s) a)
runWithRecord action store rc =
  let mkResult ((rs, reqState), newStore) = ResumableResult{wcsResponses = rc, wcsRequests = reqState, wcsFinalState = rs, wcsCheckpointStore = newStore}
  in fmap mkResult
      $ run
      $ E.runError  @e @_
      $ runReader @(Responses (Event s)) @_ rc
      $ handleLogIgnore @CheckpointLogMsg
      $ runState @CheckpointStore store
      $ runState  @(Requests (Handlers s)) mempty
      $ handleContractEffs @s @e @_ @a action

insertAndUpdate ::
  forall s e a.
  Eff (ContractEffs s e) a
  -> CheckpointStore
  -> Responses (Event s)
  -> Response (Event s)
  -> Either e (ResumableResult (Event s) (Handlers s) a)
insertAndUpdate action store record newResponse =
  runWithRecord action store (insertResponse newResponse record)

-- | The result of running a 'Resumable'
data ResumableResult i o a =
    ResumableResult
        { wcsResponses       :: Responses i -- The record with the resumable's execution history
        , wcsRequests        :: Requests o -- Handlers that the 'Resumable' has registered
        , wcsFinalState      :: Maybe a -- Final state of the 'Resumable'
        , wcsCheckpointStore :: CheckpointStore
        }
