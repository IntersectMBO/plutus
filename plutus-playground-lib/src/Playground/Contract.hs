-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}

module Playground.Contract
    ( mkFunctions
    , mkFunction
    , mkKnownCurrencies
    , ToSchema
    , Schema
    , ToJSON
    , FromJSON
    , FunctionSchema
    , Generic
    , payToPublicKey_
    , MockWallet
    , ByteString
    , printSchemas
    , printJson
    , Wallet(..)
    , addBlocksAndNotify
    , runWalletActionAndProcessPending
    , module Playground.Interpreter.Util
    , KnownCurrency
    ) where

import           Data.Aeson                  (FromJSON, ToJSON, encode)
import           Data.ByteArray              (ByteArrayAccess)
import qualified Data.ByteArray              as BA
import           Data.ByteString.Lazy        (ByteString)
import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy.Char8  as LBC8
import           Data.Swagger                (Schema, ToSchema)
import           GHC.Generics                (Generic)
import           Playground.API              (FunctionSchema, KnownCurrency)
import           Playground.Interpreter.Util
import           Playground.TH               (mkFunction, mkFunctions, mkKnownCurrencies, mkSingleFunction)
import           Wallet.API                  (payToPublicKey_)
import           Wallet.Emulator             (addBlocksAndNotify, runWalletActionAndProcessPending)
import           Wallet.Emulator.Types       (MockWallet, Wallet (..))

-- We need to work with lazy 'ByteString's in contracts,
-- but 'ByteArrayAccess' (which we need for hashing) is only defined for strict
-- ByteStrings. With this orphan instance we can use lazy ByteStrings
-- throughout.
instance ByteArrayAccess ByteString where
    length = BA.length . BSL.toStrict
    withByteArray ba = BA.withByteArray (BSL.toStrict ba)

$(mkSingleFunction 'payToPublicKey_)

printSchemas :: ([FunctionSchema Schema], [KnownCurrency]) -> IO ()
printSchemas (schemas, currencies) =
    LBC8.putStrLn . encode $ (schemas <> [payToPublicKey_Schema], currencies)

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . encode
