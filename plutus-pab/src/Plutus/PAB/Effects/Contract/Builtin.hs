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
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error               (Error, throwError)
import           Data.Aeson                              (FromJSON, ToJSON, Value)
import qualified Data.Aeson                              as JSON
import qualified Data.Aeson.Types                        as JSON
import           Data.Row
import qualified Data.Text                               as Text

import           Plutus.PAB.Effects.Contract             (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Events.Contract              (ContractPABRequest)
import qualified Plutus.PAB.Events.Contract              as C
import           Plutus.PAB.Events.ContractInstanceState (PartiallyDecodedResponse)
import qualified Plutus.PAB.Events.ContractInstanceState as C
import           Plutus.PAB.Types                        (PABError (..))

import           Playground.Schema                       (endpointsToSchemas)
import           Playground.Types                        (FunctionSchema)
import           Plutus.Contract                         (BlockchainActions, Contract)
import           Plutus.Contract.Resumable               (Response)
import           Plutus.Contract.Schema                  (Event, Handlers, Input, Output)
import           Plutus.Contract.State                   (ContractResponse (..))
import qualified Plutus.Contract.State                   as ContractState
import qualified Plutus.Trace.Emulator.Types             as Emulator
import           Schema                                  (FormSchema)

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
        -> SomeBuiltinState a

instance PABContract (Builtin a) where
    type ContractDef (Builtin a) = a
    type State (Builtin a) = SomeBuiltinState a
    serialisableState _ = getResponse

-- | Handle the 'ContractEffect' for a builtin contract type with parameter
--   @a@.
handleBuiltin ::
    forall a effs.
    Member (Error PABError) effs
    => (a -> [FunctionSchema FormSchema]) -- ^ The schema (construct with 'endpointsToSchemas'. Can also be an empty list)
    -> (a -> SomeBuiltin) -- ^ The actual contract
    -> ContractEffect (Builtin a)
    ~> Eff effs
handleBuiltin mkSchema initialise = \case
    InitialState c           -> case initialise c of SomeBuiltin c' -> initBuiltin c'
    UpdateContract _ state p -> case state of SomeBuiltinState s -> updateBuiltin s p
    ExportSchema a           -> pure $ mkSchema a

getResponse :: forall a. SomeBuiltinState a -> PartiallyDecodedResponse ContractPABRequest
getResponse (SomeBuiltinState s) =
    mkResponse
    $ ContractState.mkResponse
    $ Emulator.instContractState
    $ Emulator.toInstanceState s

initBuiltin ::
    forall effs a w schema error b.
    ContractConstraints w schema error
    => Contract w schema error b
    -> Eff effs (SomeBuiltinState a)
initBuiltin = pure . SomeBuiltinState . Emulator.emptyInstanceState

updateBuiltin ::
    forall effs a w schema error b.
    ( ContractConstraints w schema error
    , Member (Error PABError) effs
    )
    => Emulator.ContractInstanceStateInternal w schema error b
    -> Response C.ContractResponse
    -> Eff effs (SomeBuiltinState a)
updateBuiltin oldState event = do
    resp <- traverse toEvent event
    let newState = Emulator.addEventInstanceState resp oldState
    case newState of
        Just k -> pure (SomeBuiltinState k)
        _      -> throwError $ ContractCommandError 0 "failed to update contract"

toEvent ::
    forall schema effs.
    ( Member (Error PABError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    )
    => C.ContractResponse
    -> Eff effs (Event schema)
toEvent = fromJSON . JSON.toJSON . C.ContractHandlersResponse

mkResponse ::
    forall w schema err.
    ( Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    , ToJSON err
    , ToJSON w
    )
    => ContractResponse w err (Event schema) (Handlers schema)
    -> PartiallyDecodedResponse ContractPABRequest
mkResponse ContractResponse{newState, hooks, logs, observableState, err} =
    C.PartiallyDecodedResponse
        { C.newState = fmap JSON.toJSON newState
        , C.hooks    = fmap (fmap (encodeRequest @schema)) hooks
        , C.logs     = logs
        , C.observableState = JSON.toJSON observableState
        , C.err = fmap JSON.toJSON err
        }

encodeRequest ::
    forall schema.
    ( Forall (Output schema) ToJSON
    )
    => Handlers schema
    -> ContractPABRequest
encodeRequest = either error C.unContractHandlerRequest . JSON.eitherDecode . JSON.encode

fromJSON :: (Member (Error PABError) effs, FromJSON a) => Value -> Eff effs a
fromJSON =
    either (throwError . OtherError . Text.pack) pure
    . JSON.parseEither JSON.parseJSON
