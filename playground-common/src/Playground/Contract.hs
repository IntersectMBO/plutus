-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}

module Playground.Contract
    ( mkFunctions
    , mkFunction
    , endpointsToSchemas
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
    , module Playground.Interpreter.Util
    , KnownCurrency(KnownCurrency)
    , ValidatorHash(ValidatorHash)
    , TokenName(TokenName)
    , NonEmpty((:|))
    , adaCurrency
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
import           GHC.Generics                                    (Generic)
import           Language.Plutus.Contract                        (AsContractError, BlockchainActions, Contract,
                                                                  Endpoint, awaitSlot, nextTransactionsAt, submitTx,
                                                                  type (.\/), utxoAt, watchAddressUntil)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (endpoint)
import           Language.Plutus.Contract.Effects.OwnPubKey      (ownPubKey)
import           Language.Plutus.Contract.Trace                  (TraceError (..))
import           Ledger.Constraints                              (modifiesUtxoSet)
import           Ledger.Interval                                 (interval)
import           Ledger.Scripts                                  (ValidatorHash (ValidatorHash))
import           Ledger.Tx                                       (Tx, TxOutRef (TxOutRef), txOutRefId)
import           Ledger.Value                                    (TokenName (TokenName))
import           Playground.Interpreter.Util
import           Playground.Schema                               (endpointsToSchemas)
import           Playground.TH                                   (ensureKnownCurrencies, mkFunction, mkFunctions,
                                                                  mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types                                (Expression, FunctionSchema,
                                                                  KnownCurrency (KnownCurrency), adaCurrency)
import           Schema                                          (FormSchema, ToArgument, ToSchema)
import           Wallet.Emulator.Types                           (Wallet (..))

printSchemas :: ([FunctionSchema FormSchema], [KnownCurrency]) -> IO ()
printSchemas (userSchemas, currencies) =
    LBC8.putStrLn . JSON.encode $ (allSchemas, currencies)
  where
    allSchemas = userSchemas <> builtinSchemas
    builtinSchemas = []

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . JSON.encode
