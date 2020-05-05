{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternGuards      #-}
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
    -- * Output produced by contracts
    , decodeContractRequests
    -- * Experimental / misc.
    , invokeContractUpdate_
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error                       (Error, throwError)
import           Control.Monad.Freer.TH                          (makeEffect)
import           Data.Aeson                                      ((.=))
import qualified Data.Aeson                                      as JSON
import qualified Data.HashMap.Lazy                               as HashMap
import           Data.Text                                       (Text)
import qualified Data.Text                                       as Text
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription (..))
import           Language.Plutus.Contract.Resumable              (Response (..))
import           Playground.Types                                (FunctionSchema)

import           Language.Plutus.Contract.State                  (ContractRequest (..))
import           Plutus.SCB.Events.Contract                      (ContractResponse (..), ContractSCBRequest (..),
                                                                  PartiallyDecodedResponse (..))
import           Plutus.SCB.Types                                (SCBError (OtherError))
import           Schema                                          (FormSchema)

-- | Commands to update a contract. 't' identifies the contract.
data ContractCommand t
    = InitContract t
    | UpdateContract t (ContractRequest JSON.Value)
    deriving (Show, Eq)

data ContractEffect t r where
    ExportSchema :: t -> ContractEffect t [FunctionSchema FormSchema]
    InvokeContract :: ContractCommand t -> ContractEffect  t (PartiallyDecodedResponse ContractSCBRequest)
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
    -> (PartiallyDecodedResponse ContractSCBRequest)
    -- ^ The last state of the contract
    -> EventPayload -- TODO: Change JSON.Value in 'UpdateContract' to Payload and move some of invokeContractUpdate_ into there?
    -- ^ The actual update
    -> Eff effs (PartiallyDecodedResponse ContractSCBRequest)
invokeContractUpdate_ contract PartiallyDecodedResponse{newState=oldState} payload =
    invokeContract
        $ UpdateContract contract
        $ ContractRequest{oldState=oldState, event=unEventPayload payload}

-- | Examine the 'hooks' JSON object and extract from it the
--   list of 'ContractRequest' values issued by the contract
decodeContractRequests ::
    ( Member (Error SCBError) effs)
    => (PartiallyDecodedResponse JSON.Value)
    -> Eff effs (PartiallyDecodedResponse ContractSCBRequest)
decodeContractRequests = traverse ex
    where ex (JSON.Object mp)
                | [(key, value)] <- HashMap.toList mp = handleHookEntry key value
          ex _ = throwError (OtherError "Failed to parse old contract state")

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
    -> Eff effs ContractSCBRequest -- FIXME Request (Either ContractSCBRequest JSON.Value)
handleHookEntry "utxo-at" obj         = withAesonResult $ UtxoAtRequest <$> JSON.fromJSON obj
handleHookEntry "tx-confirmation" obj = withAesonResult $ AwaitTxConfirmedRequest <$> JSON.fromJSON obj
handleHookEntry "own-pubkey" obj      = withAesonResult $ OwnPubkeyRequest <$> JSON.fromJSON obj
handleHookEntry "address" obj         = withAesonResult $ NextTxAtRequest <$> JSON.fromJSON obj
handleHookEntry "tx" obj              = withAesonResult $ WriteTxRequest <$> JSON.fromJSON obj
handleHookEntry "slot" obj            = withAesonResult $ AwaitSlotRequest <$> JSON.fromJSON obj
handleHookEntry _ obj                 = withAesonResult $ UserEndpointRequest <$> JSON.fromJSON obj

contractMessageToPayload :: Response ContractResponse -> EventPayload
contractMessageToPayload = EventPayload . fmap go where
    go = JSON.object . (\(tag, vl) -> ["tag" .= tag, "value" .= vl]) . \case
        AwaitSlotResponse slot -> ("slot", JSON.toJSON slot)
        AwaitTxConfirmedResponse txid -> ("tx-confirmation", JSON.toJSON txid)
        OwnPubkeyResponse pk -> ("own-pubkey", JSON.toJSON pk)
        UtxoAtResponse u -> ("utxo-at", JSON.toJSON u)
        NextTxAtResponse tx -> ("address", JSON.toJSON tx)
        WriteTxResponse r -> ("tx", JSON.toJSON r)
        UserEndpointResponse (EndpointDescription n) r -> (n, JSON.toJSON r)
