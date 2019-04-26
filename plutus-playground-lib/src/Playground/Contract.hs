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
    ) where

import           Data.Aeson                  (FromJSON, ToJSON, encode)
import           Data.ByteArray              (ByteArrayAccess)
import qualified Data.ByteArray              as BA
import           Data.ByteString.Lazy        (ByteString)
import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy.Char8  as LBC8
import           Data.List.NonEmpty          (NonEmpty ((:|)))
import           Data.Swagger                (Schema, ToSchema)
import           GHC.Generics                (Generic)
import           Ledger.Validation           (ValidatorHash (ValidatorHash))
import           Ledger.Value                (TokenName (TokenName), Value)
import           Playground.API              (FunctionSchema, KnownCurrency (KnownCurrency), adaCurrency)
import           Playground.Interpreter.Util
import           Playground.TH               (mkFunction, mkFunctions, mkKnownCurrencies, mkSingleFunction)
import           Wallet.API                  (SlotRange, WalletAPI, payToPublicKey_)
import           Wallet.Emulator             (addBlocksAndNotify, runWalletActionAndProcessPending, walletPubKey)
import           Wallet.Emulator.Types       (MockWallet, Wallet (..))

payToWallet_ :: (Monad m, WalletAPI m) => SlotRange -> Value -> Wallet -> m ()
payToWallet_ r v = payToPublicKey_ r v . walletPubKey

-- We need to work with lazy 'ByteString's in contracts,
-- but 'ByteArrayAccess' (which we need for hashing) is only defined for strict
-- ByteStrings. With this orphan instance we can use lazy ByteStrings
-- throughout.
instance ByteArrayAccess ByteString where
    length = BA.length . BSL.toStrict
    withByteArray ba = BA.withByteArray (BSL.toStrict ba)

$(mkSingleFunction 'payToWallet_)

printSchemas :: ([FunctionSchema Schema], [KnownCurrency]) -> IO ()
printSchemas (schemas, currencies) =
    LBC8.putStrLn . encode $ (schemas <> [payToWallet_Schema], currencies)

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . encode
