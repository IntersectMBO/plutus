{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-

Builtin contracts that are compiled together with the PAB.

-}
module Plutus.PAB.Effects.Contract.Builtin(
    Builtin
    , ContractConstraints
    , SomeBuiltin(..)
    , handleBuiltin
    -- * Extracting schemas from contracts
    , type (.\\)
    , type (.\/)
    , BlockchainActions
    , Empty
    , endpointsToSchemas
    , getResponse
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error                        (Error, throwError)
import           Control.Monad.Freer.Extras.Log                   (LogMsg (..), logDebug)
import           Data.Aeson                                       (FromJSON, ToJSON, Value)
import qualified Data.Aeson                                       as JSON
import qualified Data.Aeson.Types                                 as JSON
import           Data.Bifunctor                                   (Bifunctor (..))
import           Data.Foldable                                    (traverse_)
import           Data.Row
import qualified Data.Text                                        as Text

import           Plutus.Contract.Types                            (ResumableResult (..), SuspendedContract (..))
import           Plutus.PAB.Effects.Contract                      (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Events.Contract                       (ContractPABRequest)
import qualified Plutus.PAB.Events.Contract                       as C
import           Plutus.PAB.Monitoring.PABLogMsg                  (PABMultiAgentMsg (..))
import           Plutus.PAB.Types                                 (PABError (..))

import           Playground.Schema                                (endpointsToSchemas)
import           Playground.Types                                 (FunctionSchema)
import           Plutus.Contract                                  (BlockchainActions, Contract, ContractInstanceId)
import           Plutus.Contract.Resumable                        (Response)
import           Plutus.Contract.Schema                           (Event, Input, Output)
import           Plutus.Contract.State                            (ContractResponse (..))
import qualified Plutus.Contract.State                            as ContractState
import           Plutus.PAB.Core.ContractInstance.RequestHandlers (ContractInstanceMsg (ContractLog, ProcessFirstInboxMessage))
import           Plutus.Trace.Emulator.Types                      (ContractInstanceStateInternal (..))
import qualified Plutus.Trace.Emulator.Types                      as Emulator
import           Schema                                           (FormSchema)

-- | Contracts that are built into the PAB (ie. compiled with it) and receive
--   an initial value of type 'a'.
data Builtin a

type ContractConstraints w schema error =
    ( Monoid w
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    , Forall (Input schema) FromJSON
    , ToJSON error
    , ToJSON w
    , FromJSON w
    , AllUniqueLabels (Input schema)
    )

-- | Plutus contract with all parameters existentially quantified. Can be any contract that satisfies the
--   'ContractConstraints'.
data SomeBuiltin where
    SomeBuiltin :: forall w schema error a. ContractConstraints w schema error => Contract w schema error a -> SomeBuiltin

data SomeBuiltinState a where
    SomeBuiltinState ::
        forall a w schema error b.
        ContractConstraints w schema error
        => Emulator.ContractInstanceStateInternal w schema error b -- ^ Internal state
        -> w -- ^ Observable state (stored separately)
        -> SomeBuiltinState a

instance PABContract (Builtin a) where
    type ContractDef (Builtin a) = a
    type State (Builtin a) = SomeBuiltinState a
    serialisableState _ = getResponse

-- | Handle the 'ContractEffect' for a builtin contract type with parameter
--   @a@.
handleBuiltin ::
    forall a effs.
    ( Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    )
    => (a -> [FunctionSchema FormSchema]) -- ^ The schema (construct with 'endpointsToSchemas'. Can also be an empty list)
    -> (a -> SomeBuiltin) -- ^ The actual contract
    -> ContractEffect (Builtin a)
    ~> Eff effs
handleBuiltin mkSchema initialise = \case
    InitialState i c           -> case initialise c of SomeBuiltin c' -> initBuiltin i c'
    UpdateContract i _ state p -> case state of SomeBuiltinState s w -> updateBuiltin i s w p
    ExportSchema a             -> pure $ mkSchema a

getResponse :: forall a. SomeBuiltinState a -> ContractResponse Value Value Value ContractPABRequest
getResponse (SomeBuiltinState s w) =
    bimap JSON.toJSON (C.unContractHandlerRequest . fromJSON' . JSON.toJSON)
    $ ContractState.mapE JSON.toJSON
    $ ContractState.mapW JSON.toJSON
    $ ContractState.mkResponse w
    $ Emulator.instContractState
    $ Emulator.toInstanceState s

initBuiltin ::
    forall effs a w schema error b.
    ( ContractConstraints w schema error
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    )
    => ContractInstanceId
    -> Contract w schema error b
    -> Eff effs (SomeBuiltinState a)
initBuiltin i con = do
    let initialState = Emulator.emptyInstanceState con
    logNewMessages @a i initialState
    pure $ SomeBuiltinState initialState mempty

updateBuiltin ::
    forall effs a w schema error b.
    ( ContractConstraints w schema error
    , Member (Error PABError) effs
    , Member (LogMsg (PABMultiAgentMsg (Builtin a))) effs
    )
    => ContractInstanceId
    -> Emulator.ContractInstanceStateInternal w schema error b
    -> w
    -> Response C.ContractPABResponse
    -> Eff effs (SomeBuiltinState a)
updateBuiltin i oldState oldW event = do
    resp <- traverse toEvent event
    let newState = Emulator.addEventInstanceState resp oldState
    case newState of
        Just k -> do
            logDebug @(PABMultiAgentMsg (Builtin a)) (ContractInstanceLog $ ProcessFirstInboxMessage i event)
            logNewMessages @a i k
            let newW = oldW <> (_lastState $ _resumableResult $ Emulator.cisiSuspState oldState)
            pure (SomeBuiltinState k newW)
        _      -> throwError $ ContractCommandError 0 "failed to update contract"

logNewMessages ::
    forall b w s e a effs.
    ( Member (LogMsg (PABMultiAgentMsg (Builtin b))) effs
    )
    => ContractInstanceId
    -> ContractInstanceStateInternal w s e a
    -> Eff effs ()
logNewMessages i ContractInstanceStateInternal{cisiSuspState=SuspendedContract{_resumableResult=ResumableResult{_lastLogs, _observableState}}} = do
    traverse_ (send @(LogMsg (PABMultiAgentMsg (Builtin b))) . LMessage . fmap (ContractInstanceLog . ContractLog i)) _lastLogs

toEvent ::
    forall schema effs.
    ( Member (Error PABError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    )
    => C.ContractPABResponse
    -> Eff effs (Event schema)
toEvent = fromJSON . JSON.toJSON . C.ContractHandlersResponse

fromJSON :: (Member (Error PABError) effs, FromJSON a) => Value -> Eff effs a
fromJSON =
    either (throwError . OtherError . Text.pack) pure
    . JSON.parseEither JSON.parseJSON

fromJSON' :: FromJSON a => Value -> a
fromJSON' = either (\x -> error $ "fromJSON'" <> show x) id . JSON.parseEither JSON.parseJSON
