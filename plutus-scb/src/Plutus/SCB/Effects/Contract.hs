{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternGuards      #-}
{-# LANGUAGE StrictData         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}
module Plutus.SCB.Effects.Contract(
    ContractCommand(..)
    , ContractEffect(..)
    , invokeContract
    , exportSchema
    -- * Input fed to contracts
    , EventPayload(..)
    , contractMessageToPayload
    -- * Experimental / misc.
    , invokeContractUpdate_
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.TH                          (makeEffect)
import           Data.Aeson                                      ((.=))
import qualified Data.Aeson                                      as JSON
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (..))
import           Language.Plutus.Contract.Resumable              (Response (..))
import           Playground.Types                                (FunctionSchema)

import           Language.Plutus.Contract.State                  (ContractRequest (..))
import           Plutus.SCB.Events.Contract                      (ContractHandlersResponse, ContractResponse (..),
                                                                  ContractSCBRequest (..),
                                                                  PartiallyDecodedResponse (..),
                                                                  unContractHandlersResponse)
import           Schema                                          (FormSchema)

-- | Commands to update a contract. 't' identifies the contract.
data ContractCommand t
    = InitContract t
    | UpdateContract t (ContractRequest JSON.Value)
    deriving (Show, Eq)

data ContractEffect t r where
    ExportSchema :: t -> ContractEffect t [FunctionSchema FormSchema]
    InvokeContract :: ContractCommand t -> ContractEffect t (PartiallyDecodedResponse ContractHandlersResponse)
makeEffect ''ContractEffect

-- TODO: Make a JSON value out of the response
-- in a way that is compatible with the json format expected by the
-- contract.

-- | An event sent to the contract
newtype EventPayload = EventPayload { unEventPayload :: Response JSON.Value }
    deriving stock Show

-- | Given a contract definition 't' and the contract's previous state
--   in form of a 'PartiallyDecodedResponse', apply the next input
--   event ('EventPayload') to the contract and return a
--   'PartiallyDecodedResponse' containing the new state and new hooks.
invokeContractUpdate_ ::
       (Member (ContractEffect t) effs)
    => t
    -- ^ The contract
    -> PartiallyDecodedResponse ContractSCBRequest
    -- ^ The last state of the contract
    -> EventPayload -- TODO: Change JSON.Value in 'UpdateContract' to Payload and move some of invokeContractUpdate_ into there?
    -- ^ The actual update
    -> Eff effs (PartiallyDecodedResponse ContractSCBRequest)
invokeContractUpdate_ contract PartiallyDecodedResponse {newState = oldState} (EventPayload payload) =
    fmap unContractHandlersResponse <$>
    invokeContract
        (UpdateContract contract $
         ContractRequest {oldState = oldState, event = payload})

contractMessageToPayload :: Response ContractResponse -> EventPayload
contractMessageToPayload = EventPayload . fmap go where
    go = JSON.object . (\(tag, vl) -> ["tag" .= tag, "value" .= vl]) . \case
        AwaitSlotResponse slot                         -> ("slot", JSON.toJSON slot)
        AwaitTxConfirmedResponse txid                  -> ("tx-confirmation", JSON.toJSON txid)
        OwnPubkeyResponse pk                           -> ("own-pubkey", JSON.toJSON pk)
        UtxoAtResponse u                               -> ("utxo-at", JSON.toJSON u)
        NextTxAtResponse tx                            -> ("address", JSON.toJSON tx)
        WriteTxResponse r                              -> ("tx", JSON.toJSON r)
        UserEndpointResponse (EndpointDescription n) r -> (n, JSON.toJSON r)
        OwnInstanceResponse r                          -> ("own-instance-id", JSON.toJSON r)
        NotificationResponse r                         -> ("notify", JSON.toJSON r)
