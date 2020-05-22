{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
module Plutus.SCB.Effects.Contract(
    ContractCommand(..)
    , ContractEffect(..)
    , invokeContract
    , exportSchema
    -- * Input fed to contracts
    , EventPayload(..)
    , encodePayload
    , contractMessageToPayload
    -- * Output produced by contracts
    , decodeContractRequests
    -- * Experimental / misc.
    , invokeContractUpdate_
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error  (Error, throwError)
import           Control.Monad.Freer.TH     (makeEffect)
import qualified Data.Aeson                 as JSON
import qualified Data.HashMap.Lazy          as HashMap
import           Data.Text                  (Text)
import qualified Data.Text                  as Text
import           Playground.Types           (FunctionSchema)
import           Plutus.SCB.Events.Contract (ContractRequest (..), ContractResponse (..), PartiallyDecodedResponse (..))
import           Plutus.SCB.Types           (SCBError (ContractCommandError, OtherError))
import           Schema                     (FormSchema)

-- | Commands to update a contract. 't' identifies the contract.
data ContractCommand t
    = InitContract t
    | UpdateContract t JSON.Value
    deriving (Show, Eq)

data ContractEffect t r where
    InvokeContract :: ContractCommand t -> ContractEffect t (Either Text PartiallyDecodedResponse)
    ExportSchema :: t -> ContractEffect t [FunctionSchema FormSchema]
makeEffect ''ContractEffect

-- TODO: Make a JSON value out of the response
-- in a way that is compatible with the json format expected by the
-- contract.

-- | An event sent to the contract
data EventPayload = EventPayload { endpointName :: Text, endpointValue :: JSON.Value }

encodePayload :: EventPayload -> (Text, JSON.Value)
encodePayload EventPayload{endpointName, endpointValue} =
    ( "event"
    , JSON.object [("tag", JSON.String endpointName), ("value", endpointValue)])

-- | Given a contract definition 't' and the contract's previous state
--   in form of a 'PartiallyDecodedResponse', apply the next input
--   event ('EventPayload') to the contract and return a
--   'PartiallyDecodedResponse' containing the new state and new hooks.
invokeContractUpdate_ ::
       (Member (ContractEffect t) effs, Member (Error SCBError) effs)
    => t
    -- ^ The contract
    -> PartiallyDecodedResponse
    -- ^ The last state of the contract
    -> EventPayload -- TODO: Change JSON.Value in 'UpdateContract' to Payload and move some of invokeContractUpdate_ into there?
    -- ^ The actual update
    -> Eff effs PartiallyDecodedResponse
invokeContractUpdate_ contract PartiallyDecodedResponse {newState = oldState} payload = do
    response <-
        invokeContract $
        UpdateContract contract $
        JSON.object [("oldState", oldState), encodePayload payload]
    case response of
        Right value -> pure value
        Left err    -> throwError $ ContractCommandError 1 err

-- | Examine the 'hooks' JSON object and extract from it the
--   list of 'ContractRequest' values issued by the contract
decodeContractRequests ::
    ( Member (Error SCBError) effs)
    => PartiallyDecodedResponse
    -> Eff effs [ContractRequest]
decodeContractRequests PartiallyDecodedResponse{hooks} =
    case hooks of
        JSON.Object mp -> traverse (uncurry handleHookEntry) (HashMap.toList mp)
        _              -> throwError (OtherError "Failed to parse old contract state")

withAesonResult ::
    ( Member (Error SCBError) effs)
    => JSON.Result a
    -> Eff effs a
withAesonResult = \case
    JSON.Error e -> throwError $ OtherError $ Text.pack e
    JSON.Success a -> pure a

-- TODO: Use symbols instead of magic strings
handleHookEntry ::
    ( Member (Error SCBError) effs)
    => Text
    -> JSON.Value
    -> Eff effs ContractRequest
handleHookEntry "utxo-at" obj         = withAesonResult $ UtxoAtRequest <$> JSON.fromJSON obj
handleHookEntry "tx-confirmation" obj = withAesonResult $ AwaitTxConfirmedRequest <$> JSON.fromJSON obj
handleHookEntry "own-pubkey" obj      = withAesonResult $ OwnPubkeyRequest <$> JSON.fromJSON obj
handleHookEntry "address" obj         = withAesonResult $ NextTxAtRequest <$> JSON.fromJSON obj
handleHookEntry "tx" obj              = withAesonResult $ WriteTxRequest <$> JSON.fromJSON obj
handleHookEntry "slot" obj            = withAesonResult $ AwaitSlotRequest <$> JSON.fromJSON obj
handleHookEntry _ obj                 = withAesonResult $ UserEndpointRequest <$> JSON.fromJSON obj

contractMessageToPayload :: ContractResponse -> EventPayload
contractMessageToPayload = \case
    AwaitSlotResponse slot -> EventPayload "slot" (JSON.toJSON slot)
    AwaitTxConfirmedResponse txid -> EventPayload "tx-confirmation" (JSON.toJSON txid)
    OwnPubkeyResponse pk -> EventPayload "own-pubkey" (JSON.toJSON pk)
    UtxoAtResponse u -> EventPayload "utxo-at" (JSON.toJSON u)
    NextTxAtResponse address tx -> EventPayload "address" (JSON.toJSON (address, tx))
    WriteTxResponse r -> EventPayload "tx" (JSON.toJSON r)
    UserEndpointResponse n r -> EventPayload n (JSON.toJSON r)
