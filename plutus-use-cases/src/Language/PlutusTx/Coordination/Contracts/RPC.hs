{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
module Language.PlutusTx.Coordination.Contracts.RPC where

import qualified Control.Monad                        as Monad
import           Data.Aeson                           (FromJSON, ToJSON)
import           GHC.Generics                         (Generic)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects.RPC

data Adder

instance RPC Adder where
    type RPCRequest Adder = (Integer, Integer)
    type RPCRequestEndpoint Adder = "add"
    type RPCResponse Adder = Integer
    type RPCResponseEndpoint Adder = "add-response"
    type RPCError Adder = CancelRPC

type AdderSchema =
    BlockchainActions
        .\/ Endpoint "target instance" ContractInstanceId
        .\/ Endpoint "serve" ()
        .\/ RPCClient Adder
        .\/ RPCServer Adder

data AdderError =
    AdderCallRPCError RPCCallError
    | AdderRespondRPCError RPCRespondError
    | AdderContractError ContractError
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data CancelRPC = CancelRPC
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Contract that calls the RPC (client)
callAdder :: Contract AdderSchema AdderError (Either CancelRPC Integer)
callAdder = do
    instanceId <- mapError AdderContractError $ endpoint @"target instance"
    logInfo @String $ "Calling contract " <> show instanceId
    result <- mapError AdderCallRPCError $ callRPC @Adder NoRetries instanceId (2, 2)
    logInfo @String $ "2+2=" <> show result
    return result

callAdderCancel :: Contract AdderSchema AdderError (Either CancelRPC Integer)
callAdderCancel = do
    instanceId <- mapError AdderContractError $ endpoint @"target instance"
    logInfo @String $ "Calling contract " <> show instanceId
    result <- mapError AdderCallRPCError $ callRPC @Adder NoRetries instanceId (10, 2)
    logInfo @String $ "10+2=" <> show result
    return result

-- | Contract that responds to the RPC (server)
respondAdder :: Contract AdderSchema AdderError ()
respondAdder = do
    _ <- mapError AdderContractError $ endpoint @"serve"
    mapError AdderRespondRPCError
        $ respondRPC @Adder $ \(a, b) -> do
            logInfo @String "Responding to RPC"
            Monad.when (a == 10) (throwError CancelRPC)
            pure (a + b)
