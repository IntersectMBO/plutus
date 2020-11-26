-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}

module Playground.Contract
    ( mkFunctions
    , mkFunction
    , mkIotsDefinitions
    , endpointsToSchemas
    , ensureIotsDefinitions
    , ensureKnownCurrencies
    , mkSchemaDefinitions
    , mkKnownCurrencies
    , ToSchema
    , ToArgument
    , ToJSON
    , FromJSON
    , FunctionSchema
    , FormSchema
    , Generic
    , printSchemas
    , printJson
    , IO
    , Show
    , Wallet(..)
    , runTraceWithDistribution
    , addBlocksAndNotify
    , module Playground.Interpreter.Util
    , KnownCurrency(KnownCurrency)
    , ValidatorHash(ValidatorHash)
    , TokenName(TokenName)
    , NonEmpty((:|))
    , adaCurrency
    , module IOTS
    , endpoint
    , Contract
    , Endpoint
    , AsContractError
    , TraceError(..)
    , type (.\/)
    , interval
    , ownPubKey
    , BlockchainActions
    , awaitSlot
    , modifiesUtxoSet
    , nextTransactionsAt
    , utxoAt
    , watchAddressUntil
    , submitTx
    , Tx
    , TxOutRef(TxOutRef, txOutRefId)
    , Expression
    ) where

import           Data.Aeson                                      (FromJSON, ToJSON)
import qualified Data.Aeson                                      as JSON
import qualified Data.ByteString.Lazy.Char8                      as LBC8
import           Data.List.NonEmpty                              (NonEmpty ((:|)))
import           Data.Text                                       (Text)
import           GHC.Generics                                    (Generic)
import           IOTS                                            (IotsType (iotsDefinition))
import           Language.Plutus.Contract                        (AsContractError, BlockchainActions, Contract,
                                                                  Endpoint, awaitSlot, nextTransactionsAt, submitTx,
                                                                  type (.\/), utxoAt, watchAddressUntil)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (endpoint)
import           Language.Plutus.Contract.Effects.OwnPubKey      (ownPubKey)
import           Language.Plutus.Contract.Trace                  (TraceError (..), runTraceWithDistribution)
import           Ledger.Constraints                              (modifiesUtxoSet)
import           Ledger.Interval                                 (interval)
import           Ledger.Scripts                                  (ValidatorHash (ValidatorHash))
import           Ledger.Tx                                       (Tx, TxOutRef (TxOutRef), txOutRefId)
import           Ledger.Value                                    (TokenName (TokenName))
import           Playground.Interpreter.Util
import           Playground.Schema                               (endpointsToSchemas)
import           Playground.TH                                   (ensureIotsDefinitions, ensureKnownCurrencies,
                                                                  mkFunction, mkFunctions, mkIotsDefinitions,
                                                                  mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types                                (Expression, FunctionSchema,
                                                                  KnownCurrency (KnownCurrency), adaCurrency)
import           Schema                                          (FormSchema, ToArgument, ToSchema)
import           Wallet.Emulator                                 (addBlocksAndNotify)
import           Wallet.Emulator.Types                           (Wallet (..))

printSchemas :: ([FunctionSchema FormSchema], [KnownCurrency], Text) -> IO ()
printSchemas (userSchemas, currencies, iotsDefinitions) =
    LBC8.putStrLn . JSON.encode $ (allSchemas, currencies, iotsDefinitions)
  where
    allSchemas = userSchemas <> builtinSchemas
    builtinSchemas = []

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . JSON.encode
