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

"inline" contracts from plutus-use-cases for testing

-}
module Plutus.PAB.Effects.Contract.ContractTest(
    TestContracts(..)
    , handleContractTest
    ) where

import           Control.Monad.Freer
import           Control.Monad.Freer.Error                   (Error)
import           Data.Aeson                                  (FromJSON, ToJSON)
import           Data.Bifunctor                              (Bifunctor (..))
import           Data.Row
import           Data.Text.Prettyprint.Doc
import           Data.Void                                         (Void, absurd)
import           GHC.Generics                                      (Generic)

import           Data.Text.Extras                                  (tshow)
import           Plutus.PAB.Effects.Contract                       (ContractEffect (..), PABContract (..))
import           Plutus.PAB.Events.Contract                        (ContractPABRequest)
import qualified Plutus.PAB.Events.Contract                        as C
import           Plutus.PAB.Events.ContractInstanceState           (PartiallyDecodedResponse)
import qualified Plutus.PAB.Events.ContractInstanceState           as C
import           Plutus.PAB.Types                                  (PABError (..))

import           Control.Monad.Freer.Extras.Log                    (LogMsg, logDebug)

import           Plutus.Contract                          (BlockchainActions, Contract, ContractError)
import           Plutus.Contract.Effects.RPC              (RPCClient)
import           Plutus.Contract.Resumable                (Response)
import           Plutus.Contract.Schema                   (Event, Handlers, Input, Output)
import           Plutus.Contract.State                    (ContractRequest (..), ContractResponse (..))
import qualified Plutus.Contract.State                    as ContractState
import qualified Plutus.Contracts.Currency as Contracts.Currency
import qualified Plutus.Contracts.Game     as Contracts.Game
import qualified Plutus.Contracts.RPC      as Contracts.RPC
import           Playground.Schema                                 (endpointsToSchemas)
import qualified Plutus.PAB.Effects.ContractTest.AtomicSwap        as Contracts.AtomicSwap
import qualified Plutus.PAB.Effects.ContractTest.PayToWallet       as Contracts.PayToWallet

data TestContracts = Game | Currency | AtomicSwap | PayToWallet | RPCClient | RPCServer
    deriving (Eq, Ord, Show, Generic)
    deriving anyclass (FromJSON, ToJSON)

instance Pretty TestContracts where
    pretty = viaShow

-- | A mock/test handler for 'ContractEffect'. Uses 'Plutus.PAB.Effects.Contract.Builtin'.
handleContractTest ::
    ( Member (Error PABError) effs
    )
    => ContractEffect (Builtin TestContracts)
    ~> Eff effs
handleContractTest = Builtin.handleBuiltin getSchema getContract

getSchema :: TestContracts -> [FunctionSchema FormSchema]
getSchema = \case
    Game        -> Builtin.endpointsToSchemas @(Contracts.Game.GameSchema .\\ BlockchainActions)
    Currency    -> Builtin.endpointsToSchemas @(Contracts.Currency.CurrencySchema .\\ BlockchainActions)
    AtomicSwap  -> Builtin.endpointsToSchemas @(Contracts.AtomicSwap.AtomicSwapSchema .\\ BlockchainActions)
    PayToWallet -> Builtin.endpointsToSchemas @(Contracts.PayToWallet.PayToWalletSchema .\\ BlockchainActions)
    RPCClient   -> adderSchema
    RPCServer   -> adderSchema
    where
        adderSchema = Builtin.endpointsToSchemas @(Contracts.RPC.AdderSchema .\\ (BlockchainActions .\/ RPCClient Contracts.RPC.Adder))

getContract :: TestContracts -> SomeBuiltin
getContract = \case
    Game        -> SomeBuiltin game
    Currency    -> SomeBuiltin currency
    AtomicSwap  -> SomeBuiltin swp
    PayToWallet -> SomeBuiltin payToWallet
    RPCClient   -> SomeBuiltin rpcClient
    RPCServer   -> SomeBuiltin rpcServer
    where
        game = Contracts.Game.game @ContractError
        currency = Contracts.Currency.forgeCurrency
        swp = first tshow Contracts.AtomicSwap.atomicSwap
        payToWallet = first tshow Contracts.PayToWallet.payToWallet
        rpcClient = first tshow $ void Contracts.RPC.callAdder
        rpcServer = first tshow $ void Contracts.RPC.respondAdder
        adderSchema = endpointsToSchemas @(Contracts.RPC.AdderSchema .\\ (BlockchainActions .\/ RPCClient Contracts.RPC.Adder))

doContractInit ::
    forall w schema effs.
    ( Member (Error PABError) effs
    , Forall (Output schema) ToJSON
    , Forall (Input schema) ToJSON
    , Monoid w
    , ToJSON w
    )
    => Contract w schema Text ()
    -> Eff effs (PartiallyDecodedResponse ContractPABRequest)
doContractInit contract = either throwError pure $ do
    let value = ContractState.initialiseContract contract
    fromString $ fmap (fmap C.unContractHandlerRequest) $ JSON.eitherDecode $ JSON.encode value

doContractUpdate ::
    forall w schema effs.
    ( Member (Error PABError) effs
    , AllUniqueLabels (Input schema)
    , Forall (Input schema) FromJSON
    , Forall (Input schema) ToJSON
    , Forall (Output schema) ToJSON
    , Member (LogMsg ContractTestMsg) effs
    , Monoid w
    , ToJSON w
    )
    => Contract w schema Text ()
    -> PartiallyDecodedResponse ContractPABRequest
    -> Response C.ContractResponse
    -> Eff effs (PartiallyDecodedResponse ContractPABRequest)
doContractUpdate contract oldState response = do
    let C.PartiallyDecodedResponse{C.newState} = oldState
    oldState' <- traverse fromJSON newState
    typedResp <- traverse (fromJSON . JSON.toJSON . C.ContractHandlersResponse) response
    let conReq = ContractRequest{oldState = oldState', event = typedResp }
    let response' = mkResponse $ ContractState.insertAndUpdateContract contract conReq
    logDebug $ ContractTestResponse response'
    pure response'

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

