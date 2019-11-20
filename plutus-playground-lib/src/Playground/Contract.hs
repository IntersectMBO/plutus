-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
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
    , ToJSON
    , FromJSON
    , FunctionSchema
    , FormSchema
    , Generic
    , payToWallet_
    , MockWallet
    , ByteString
    , printSchemas
    , printJson
    , IO
    , Show
    , Wallet(..)
    , runTraceWithDistribution
    , addBlocksAndNotify
    , runWalletActionAndProcessPending
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
    , inputs
    , nextTransactionAt
    , utxoAt
    , validityRange
    , watchAddressUntil
    , writeTx
    , writeTxSuccess
    , Tx
    , TxOutRef(TxOutRef, txOutRefId)
    , Expression
    ) where

import           Data.Aeson                                      (FromJSON, ToJSON)
import qualified Data.Aeson                                      as JSON
import           Data.ByteArray                                  (ByteArrayAccess)
import qualified Data.ByteArray                                  as BA
import           Data.ByteString.Lazy                            (ByteString)
import qualified Data.ByteString.Lazy                            as BSL
import qualified Data.ByteString.Lazy.Char8                      as LBC8
import           Data.List.NonEmpty                              (NonEmpty ((:|)))
import           Data.Text                                       (Text)
import           GHC.Generics                                    (Generic)
import           IOTS                                            (IotsType (iotsDefinition))
import           Language.Plutus.Contract                        (type (.\/), AsContractError, BlockchainActions,
                                                                  Contract, Endpoint, awaitSlot, inputs,
                                                                  nextTransactionAt, utxoAt, validityRange,
                                                                  watchAddressUntil, writeTx, writeTxSuccess)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (endpoint)
import           Language.Plutus.Contract.Effects.OwnPubKey      (ownPubKey)
import           Language.Plutus.Contract.Trace                  (TraceError (..), runTraceWithDistribution)
import           Ledger.Interval                                 (always, interval)
import           Ledger.Scripts                                  (ValidatorHash (ValidatorHash))
import           Ledger.Tx                                       (Tx, TxOutRef (TxOutRef), txOutRefId)
import           Ledger.Value                                    (TokenName (TokenName))
import           Playground.Interpreter.Util
import           Playground.Schema                               (endpointsToSchemas)
import           Playground.TH                                   (ensureIotsDefinitions, ensureKnownCurrencies,
                                                                  mkFunction, mkFunctions, mkIotsDefinitions,
                                                                  mkKnownCurrencies, mkSchemaDefinitions,
                                                                  mkSingleFunction)
import           Playground.Types                                (Expression, FunctionSchema,
                                                                  KnownCurrency (KnownCurrency),
                                                                  PayToWalletParams (PayToWalletParams), adaCurrency,
                                                                  payTo, value)
import           Schema                                          (FormSchema, ToSchema)
import           Wallet.API                                      (WalletAPI, payToPublicKey_)
import           Wallet.Emulator                                 (addBlocksAndNotify, walletPubKey)
import qualified Wallet.Emulator                                 as Emulator
import           Wallet.Emulator.Types                           (MockWallet, Trace, Wallet (..))

payToWallet_ :: (Monad m, WalletAPI m) => PayToWalletParams -> m ()
payToWallet_ PayToWalletParams {value, payTo} =
    payToPublicKey_ always value $ walletPubKey payTo

runWalletActionAndProcessPending :: [Wallet] -> Wallet -> m a -> Trace m [Tx]
runWalletActionAndProcessPending wllts wllt a =
    fmap fst (Emulator.runWalletActionAndProcessPending wllts wllt a)

-- We need to work with lazy 'ByteString's in contracts,
-- but 'ByteArrayAccess' (which we need for hashing) is only defined for strict
-- ByteStrings. With this orphan instance we can use lazy ByteStrings
-- throughout.
instance ByteArrayAccess ByteString where
    length = BA.length . BSL.toStrict
    withByteArray ba = BA.withByteArray (BSL.toStrict ba)

$(mkSingleFunction 'payToWallet_)

printSchemas :: ([FunctionSchema FormSchema], [KnownCurrency], Text) -> IO ()
printSchemas (userSchemas, currencies, iotsDefinitions) =
    LBC8.putStrLn . JSON.encode $ (allSchemas, currencies, iotsDefinitions)
  where
    allSchemas = userSchemas <> builtinSchemas
    builtinSchemas = [payToWallet_Schema]

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . JSON.encode
