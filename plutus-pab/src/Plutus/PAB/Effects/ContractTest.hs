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
{-# LANGUAGE TypeOperators       #-}
module Plutus.PAB.Effects.ContractTest(
    TestContracts(..)
    , ContractTestMsg(..)
    , handleContractTest
    ) where

import           Control.Monad                                     (void)
import           Control.Monad.Freer
import           Control.Monad.Freer.Error                         (Error, throwError)
import           Data.Aeson                                        as JSON
import           Data.Aeson.Types                                  as JSON
import           Data.Bifunctor                                    (Bifunctor (..))
import           Data.Row
import           Data.Text                                         (Text)
import qualified Data.Text                                         as Text
import           Data.Text.Prettyprint.Doc
import           Data.Void                                         (Void, absurd)
import           GHC.Generics                                      (Generic)

import           Plutus.PAB.Effects.Contract                       (ContractCommand (..), ContractEffect (..))
import           Plutus.PAB.Events.Contract                        (ContractHandlersResponse (..), ContractPABRequest,
                                                                    PartiallyDecodedResponse)
import qualified Plutus.PAB.Events.Contract                        as C
import           Plutus.PAB.Types                                  (PABError (..))
import           Plutus.PAB.Utils                                  (tshow)

import           Control.Monad.Freer.Extra.Log                     (LogMsg, logDebug)

import           Language.Plutus.Contract                          (BlockchainActions, Contract, ContractError)
import           Language.Plutus.Contract.Effects.RPC              (RPCClient)
import           Language.Plutus.Contract.Schema                   (Event, Handlers, Input, Output)
import           Language.Plutus.Contract.State                    (ContractRequest, ContractResponse (..))
import qualified Language.Plutus.Contract.State                    as ContractState
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Contracts.Currency
import qualified Language.PlutusTx.Coordination.Contracts.Game     as Contracts.Game
import qualified Language.PlutusTx.Coordination.Contracts.RPC      as Contracts.RPC
import           Playground.Schema                                 (endpointsToSchemas)
import qualified Plutus.PAB.Effects.ContractTest.AtomicSwap        as Contracts.AtomicSwap
import qualified Plutus.PAB.Effects.ContractTest.PayToWallet       as Contracts.PayToWallet

data TestContracts = Game | Currency | AtomicSwap | PayToWallet | RPCClient | RPCServer
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

data ContractTestMsg =
    DoContractUpdate (ContractRequest Value)
    | Request (Doc Void) -- Pretty-printed 'ContractRequest schema' for some schema.
    | Response (PartiallyDecodedResponse ContractPABRequest)

instance Pretty ContractTestMsg where
    pretty = \case
        DoContractUpdate vl -> "doContractUpdate:" <+> pretty vl
        Request rq          -> "Request:" <+> fmap absurd rq
        Response rsp        -> "Response:" <+> pretty rsp

instance Pretty TestContracts where
    pretty = viaShow

-- | A mock/test handler for 'ContractEffect'
handleContractTest ::
    (Member (Error PABError) effs, Member (LogMsg ContractTestMsg) effs)
    => Eff (ContractEffect TestContracts ': effs)
    ~> Eff effs
handleContractTest = interpret $ \case
    InvokeContract (InitContract c) -> fmap ContractHandlersResponse <$> case c of
        Game        -> doContractInit game
        Currency    -> doContractInit currency
        AtomicSwap  -> doContractInit swp
        PayToWallet -> doContractInit payToWallet
        RPCClient   -> doContractInit rpcClient
        RPCServer   -> doContractInit rpcServer
    InvokeContract (UpdateContract c p) -> fmap ContractHandlersResponse <$> case c of
        Game        -> doContractUpdate game p
        Currency    -> doContractUpdate currency p
        AtomicSwap  -> doContractUpdate swp p
        PayToWallet -> doContractUpdate payToWallet p
        RPCClient   -> doContractUpdate rpcClient p
        RPCServer   -> doContractUpdate rpcServer p
    ExportSchema t -> case t of
        Game        -> pure $ endpointsToSchemas @(Contracts.Game.GameSchema .\\ BlockchainActions)
        Currency    -> pure $ endpointsToSchemas @(Contracts.Currency.CurrencySchema .\\ BlockchainActions)
        AtomicSwap  -> pure $ endpointsToSchemas @(Contracts.AtomicSwap.AtomicSwapSchema .\\ BlockchainActions)
        PayToWallet -> pure $ endpointsToSchemas @(Contracts.PayToWallet.PayToWalletSchema .\\ BlockchainActions)
        RPCClient   -> pure adderSchema
        RPCServer   -> pure adderSchema
    where
        game = first tshow $ Contracts.Game.game @ContractError
        currency = first tshow $ void Contracts.Currency.forgeCurrency
        swp = first tshow Contracts.AtomicSwap.atomicSwap
        payToWallet = first tshow Contracts.PayToWallet.payToWallet
        rpcClient = first tshow $ void Contracts.RPC.callAdder
        rpcServer = first tshow $ void Contracts.RPC.respondAdder
        adderSchema = endpointsToSchemas @(Contracts.RPC.AdderSchema .\\ (BlockchainActions .\/ RPCClient Contracts.RPC.Adder))

doContractInit ::
    forall schema effs.
    ( Member (Error PABError) effs
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    )
    => Contract schema Text ()
    -> Eff effs (PartiallyDecodedResponse ContractPABRequest)
doContractInit contract = either throwError pure $ do
    let value = ContractState.initialiseContract contract
    fromString $ fmap (fmap unContractHandlersResponse) $ JSON.eitherDecode $ JSON.encode value

doContractUpdate ::
    forall schema effs.
    ( Member (Error PABError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    , Forall (Input schema) ToJSON
    , Forall (Output schema) ToJSON
    , Forall (Input schema) Show
    , Member (LogMsg ContractTestMsg) effs
    )
    => Contract schema Text ()
    -> ContractRequest Value
    -> Eff effs (PartiallyDecodedResponse ContractPABRequest)
doContractUpdate contract payload = do
    logDebug $ DoContractUpdate payload
    request :: (ContractRequest (Event schema)) <-
        either throwError pure
        $ fromString
        $ traverse (JSON.parseEither JSON.parseJSON) payload
    logDebug $ Request $ pretty request
    let response = mkResponse $ ContractState.insertAndUpdateContract contract request
    logDebug $ Response response
    pure response

mkResponse ::
    forall schema err.
    ( Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    )
    => ContractResponse err (Event schema) (Handlers schema)
    -> PartiallyDecodedResponse ContractPABRequest
mkResponse ContractResponse{newState, hooks, logs} =
    C.PartiallyDecodedResponse
        { C.newState = fmap JSON.toJSON newState
        , C.hooks    = fmap (fmap (encodeRequest @schema)) hooks
        , C.logs     = logs
        }

encodeRequest ::
    forall schema.
    ( Forall (Output schema) ToJSON
    )
    => Handlers schema
    -> ContractPABRequest
encodeRequest = either error unContractHandlersResponse . JSON.eitherDecode . JSON.encode

fromString :: Either String a -> Either PABError a
fromString = first (ContractCommandError 0 . Text.pack)
