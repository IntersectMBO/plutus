-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE DataKinds           #-}
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
    , ensureIotsDefinitions
    , mkKnownCurrencies
    , ToSchema
    , ToJSON
    , FromJSON
    , FunctionSchema
    , Generic
    , payToWallet_
    , MockWallet
    , ByteString
    , printSchemas
    , printJson
    , Wallet(..)
    , addBlocksAndNotify
    , runWalletActionAndProcessPending
    , module Playground.Interpreter.Util
    , KnownCurrency(KnownCurrency)
    , ValidatorHash(ValidatorHash)
    , TokenName(TokenName)
    , NonEmpty((:|))
    , adaCurrency
    , module IOTS
    ) where

import           Data.Aeson                  (FromJSON, ToJSON, encode)
import           Data.ByteArray              (ByteArrayAccess)
import qualified Data.ByteArray              as BA
import           Data.ByteString.Lazy        (ByteString)
import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy.Char8  as LBC8
import           Data.List.NonEmpty          (NonEmpty ((:|)))
import           Data.Text                   (Text)
import           GHC.Generics                (Generic)
import           IOTS                        (IotsType (iotsDefinition))
import           Ledger.Interval             (always)
import           Ledger.Scripts              (ValidatorHash (ValidatorHash))
import           Ledger.Value                (TokenName (TokenName), Value)
import           Playground.API              (FunctionSchema, KnownCurrency (KnownCurrency), adaCurrency)
import           Playground.Interpreter.Util
import           Playground.TH               (ensureIotsDefinitions, mkFunction, mkFunctions, mkIotsDefinitions,
                                              mkKnownCurrencies, mkSingleFunction)
import           Schema                      (ToSchema)
import qualified Schema
import           Wallet.API                  (WalletAPI, payToPublicKey_)
import           Wallet.Emulator             (addBlocksAndNotify, runWalletActionAndProcessPending, walletPubKey)
import           Wallet.Emulator.Types       (MockWallet, Wallet (..))

payToWallet_ :: (Monad m, WalletAPI m) => Value -> Wallet -> m ()
payToWallet_ v = payToPublicKey_ always v . walletPubKey

-- We need to work with lazy 'ByteString's in contracts,
-- but 'ByteArrayAccess' (which we need for hashing) is only defined for strict
-- ByteStrings. With this orphan instance we can use lazy ByteStrings
-- throughout.
instance ByteArrayAccess ByteString where
    length = BA.length . BSL.toStrict
    withByteArray ba = BA.withByteArray (BSL.toStrict ba)

$(mkSingleFunction 'payToWallet_)

printSchemas ::
       ([FunctionSchema Schema.DataType], [KnownCurrency], Text) -> IO ()
printSchemas (userSchemas, currencies, iotsDefinitions) =
    LBC8.putStrLn . encode $ (allSchemas, currencies, iotsDefinitions)
  where
    allSchemas = userSchemas <> builtinSchemas
    builtinSchemas = [payToWallet_Schema]

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . encode
