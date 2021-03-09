{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE StrictData          #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-

Effects for running contract instances and for storing and loading their state.

-}
module Plutus.PAB.Effects.Contract(
    PABContract(..)
    , ContractEffect(..)
    , exportSchema
    , initialState
    , updateContract
    -- * Storing and retrieving contract state
    , ContractStore(..)
    , putState
    , getState
    ) where

import           Control.Monad.Freer (Eff, Member, send)
import           Playground.Types    (FunctionSchema)
import           Wallet.Types        (ContractInstanceId)

import           Schema              (FormSchema)

-- | A class of contracts running in the PAB. The purpose of the type
--   parameter @t@ is to allow for different ways of running
--   contracts, for example: A compiled executable running in a separate
--   process, or an "inline" contract that was compiled with the PAB and
--   runs in the same process.
--
--   The associated type families correspond to the type arguments needed
--   for the 'ContractRequest' and 'ContractResponse' types from
--   'Plutus.Contract.State'.
class PABContract contract where
    -- | Any data needed to identify the contract. For example, the location of the executable.
    type ContractDef contract

    -- | Type of requests sent to the contract
    type Request contract

    -- | Contract state type
    type State contract

-- data ExternalProcessContract

-- instance PABContract ExternalProcessContract where

    -- type ContractInput ExternalProcessContract = State.ContractRequest JSON.Value
    -- type ContractState

-- type Request t = State.ContractRequest (Input t)

-- -- | The state of a contract instance.
-- type State t = State.ContractResponse (ObsState t) (Err t) (IntState t) (OpenRequest t)

-- | An effect for sending updates to contracts that implement @PABContract@
data ContractEffect t r where
    ExportSchema   :: PABContract t => ContractDef t -> ContractEffect t [FunctionSchema FormSchema] -- ^ The schema of the contract
    InitialState   :: PABContract t => ContractDef t -> ContractEffect t (State t) -- ^ The initial state of the contract's instance
    UpdateContract :: PABContract t => ContractDef t -> State t -> Request t -> ContractEffect t (State t) -- ^ Send an update to the contract and return the new state.

-- | Get the schema of a contract given its definition.
exportSchema ::
    forall t effs.
    ( Member (ContractEffect t) effs
    , PABContract t
    )
    => ContractDef t
    -> Eff effs [FunctionSchema FormSchema]
exportSchema def =
    let command :: ContractEffect t [FunctionSchema FormSchema] = ExportSchema def
    in send command

-- | Get the initial state of a contract
initialState ::
    forall t effs.
    ( Member (ContractEffect t) effs
    , PABContract t
    )
    => ContractDef t
    -> Eff effs (State t)
initialState def =
    let command :: ContractEffect t (State t) = InitialState def
    in send command

-- | Send an update to the contract and return the new state.
updateContract ::
    forall t effs.
    ( Member (ContractEffect t) effs
    , PABContract t
    )
    => ContractDef t
    -> State t
    -> Request t
    -> Eff effs (State t)
updateContract def state request =
    let command :: ContractEffect t (State t) = UpdateContract def state request
    in send command

-- | Storing and retrieving the state of a contract instance
data ContractStore t r where
    PutState :: ContractDef t -> ContractInstanceId -> State t -> ContractStore t ()
    GetState :: ContractDef t -> ContractInstanceId -> ContractStore t (State t)

-- | Store the state of the contract instance
putState ::
    forall t effs.
    ( Member (ContractStore t) effs
    , PABContract t
    )
    => ContractDef t
    -> ContractInstanceId
    -> State t
    -> Eff effs ()
putState def i state =
    let command :: ContractStore t () = PutState def i state
    in send command

-- | Load the state of the contract instance
getState ::
    forall t effs.
    ( Member (ContractStore t) effs
    , PABContract t
    )
    => ContractDef t
    -> ContractInstanceId
    -> Eff effs (State t)
getState def i =
    let command :: ContractStore t (State t) = GetState def i
    in send command
