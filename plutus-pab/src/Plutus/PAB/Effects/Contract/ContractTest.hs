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
import           GHC.Generics                                (Generic)

import           Data.Text.Extras                            (tshow)
import           Playground.Types                            (FunctionSchema)
import           Plutus.Contract                             (BlockchainActions, ContractError)
import           Plutus.Contract.Effects.RPC                 (RPCClient)
import qualified Plutus.Contracts.Currency                   as Contracts.Currency
import qualified Plutus.Contracts.Game                       as Contracts.Game
import qualified Plutus.Contracts.RPC                        as Contracts.RPC
import           Plutus.PAB.Effects.Contract                 (ContractEffect (..))
import           Plutus.PAB.Effects.Contract.Builtin         (Builtin, SomeBuiltin (..))
import qualified Plutus.PAB.Effects.Contract.Builtin         as Builtin
import qualified Plutus.PAB.Effects.ContractTest.AtomicSwap  as Contracts.AtomicSwap
import qualified Plutus.PAB.Effects.ContractTest.PayToWallet as Contracts.PayToWallet
import           Plutus.PAB.Types                            (PABError (..))
import           Schema                                      (FormSchema)

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
        payToWallet =Contracts.PayToWallet.payToWallet
        rpcClient =  Contracts.RPC.callAdder
        rpcServer = Contracts.RPC.respondAdder

