{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
-- | Request-response calls to other instances
module Language.Plutus.Contract.Effects.RPC(
    RPC(..)
    , RPCClient
    , HasRPCClient
    , RPCServer
    , HasRPCServer
    , RPCParams(..)
    , RPCCallError(..)
    , RPCRespondError(..)
    , callRPC
    , respondRPC
    ) where

import           Data.Aeson                                      (FromJSON, ToJSON (toJSON))
import           Data.Void                                       (absurd)
import           GHC.Generics                                    (Generic)
import           GHC.TypeLits                                    (KnownSymbol, Symbol)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (Endpoint, HasEndpoint, endpoint)
import           Language.Plutus.Contract.Effects.Instance       (HasOwnId, ownInstanceId)
import           Language.Plutus.Contract.Effects.Notify
import           Language.Plutus.Contract.Types                  (Contract, ContractError, mapError, runError)

import           Wallet.Types                                    (ContractInstanceId, NotificationError (..))

-- $rpc
-- This module provides request-response communication between contract
-- instances, implemented using the 'Language.Plutus.Contract.Effects.Notify'
-- effect.

-- To define an RPC we need five pieces of data: The request, response, and
-- error types, the name of the endpoint that implements the RPC, and the name
-- of the endpoint that the client exposes to be notified of the result.
--
-- These pieces of data are provided by five type families: RPCRequest,
-- RPCRequestEndpoint, RPCResponse, RPCResponseEndpoint, and RPCError. This is
-- done so that the calling an RPC only requires a single type argument.
--
-- For example, the signature of a service that adds two integers would be
--
-- @
-- data Adder
--
-- type instance RPCRequest Adder = (Int, Int)
-- type instance RPCRequestEndpoint Adder = "add"
-- type instance RPCResponse Adder = Int
-- type instance RPCResponseEndpoint Adder = "add-response"
-- type instance RPCError Adder = String
-- @
--
-- We could then call the RPC with @callRPC \@Adder i (1, 2)@. The server would
-- have to define @respondRPC \@Adder (pure . uncurry (+))@.

-- NB: It would be nice if we could compute 'RPCResponseEndpoint' from
-- 'RPCRequestEndpoint' by simply adding a suffix. Unfortunately it doesn't seem
-- possible to append two symbols using 'GHC.TypeLits'.

type ToFromJSON r = (ToJSON r, FromJSON r)

class (ToFromJSON (RPCRequest r), ToFromJSON (RPCResponse r) , ToFromJSON (RPCError r)) => RPC r where
        type RPCRequest r
        type RPCError r
        type RPCRequestEndpoint r :: Symbol
        type RPCResponse r
        type RPCResponseEndpoint r :: Symbol

type RPCClient r = Endpoint (RPCResponseEndpoint r) (Either (RPCError r) (RPCResponse r))
type HasRPCClient r s = HasEndpoint (RPCResponseEndpoint r) (Either (RPCError r) (RPCResponse r)) s
type RPCServer r = Endpoint (RPCRequestEndpoint r) (RPCParams (RPCRequest r))
type HasRPCServer r s = HasEndpoint (RPCRequestEndpoint r) (RPCParams (RPCRequest r)) s

callRPC :: forall r s.
    ( HasOwnId s
    , HasEndpoint (RPCResponseEndpoint r) (Either (RPCError r) (RPCResponse r)) s
    , HasContractNotify s
    , RPC r
    , KnownSymbol (RPCRequestEndpoint r)
    )
    => ContractInstanceId
    -> RPCRequest r
    -> Contract s RPCCallError (Either (RPCError r) (RPCResponse r))
callRPC = call @(RPCRequestEndpoint r) @(RPCResponseEndpoint r) @(RPCRequest r)  @(RPCResponse r) @(RPCError r)

data RPCParams a =
    RPCParams
        { rpcCallbackInstance :: ContractInstanceId
        , rpcPayload          :: a
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Error on the RPC client side
data RPCCallError =
    RPCCallError NotificationError
    | RPCOtherError ContractError
    | RPCAwaitResponseError ContractError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Error on the RPC server side
data RPCRespondError =
    RPCEndpointError ContractError
    | RPCNotifyError NotificationError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Call another instance and return the response.
call :: forall (rpc :: Symbol) (rpcRsp :: Symbol) req resp err s.
    ( HasContractNotify s
    , HasEndpoint rpcRsp (Either err resp) s
    , HasOwnId s
    , ToJSON req
    , KnownSymbol rpc
    )
    => ContractInstanceId -- ^ ID of the contract instance that is to be called
    -> req -- ^ RPC argument
    -> Contract s RPCCallError (Either err resp)
call t req = do
    ownId <- mapError RPCOtherError ownInstanceId
    let params = RPCParams{rpcCallbackInstance = ownId, rpcPayload = req}
    _ <- mapError RPCCallError $ notifyUnsafe @rpc t (toJSON params)
    mapError RPCAwaitResponseError $ endpoint @rpcRsp

-- | Wait for another instance to call the RPC endpoint, and respond to the
--   call.
respondRPC :: forall r s.
    ( HasEndpoint (RPCRequestEndpoint r) (RPCParams (RPCRequest r)) s
    , HasContractNotify s
    , RPC r
    , KnownSymbol (RPCResponseEndpoint r)
    )
    => (RPCRequest r -> Contract s (RPCError r) (RPCResponse r)) -- ^ Implementation of the RPC
    -> Contract s RPCRespondError ()
respondRPC = respond @(RPCRequestEndpoint r) @(RPCResponseEndpoint r) @(RPCRequest r) @(RPCResponse r) @s @(RPCError r)

-- | Wait to be called by another instance.
respond :: forall (rpc :: Symbol) (rpcRespondEndpoint :: Symbol) req resp s e.
    ( HasEndpoint rpc (RPCParams req) s
    , HasContractNotify s
    , ToJSON resp
    , ToJSON e
    , KnownSymbol rpcRespondEndpoint
    )
    => (req -> Contract s e resp)
    -> Contract s RPCRespondError ()
respond k = do
    RPCParams{rpcCallbackInstance, rpcPayload} <- mapError RPCEndpointError $ endpoint @rpc
    result :: Either e resp <- mapError absurd $ runError $ k rpcPayload
    mapError RPCNotifyError $ notifyUnsafe @rpcRespondEndpoint rpcCallbackInstance (toJSON result)
