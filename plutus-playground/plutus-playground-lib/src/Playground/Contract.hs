-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}

module Playground.Contract
    ( mkFunctions
    , mkFunction
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
    ) where

import           Data.Aeson                  (FromJSON, ToJSON, encode)
import           Data.ByteArray              (ByteArrayAccess)
import qualified Data.ByteArray              as BA
import           Data.ByteString.Lazy        (ByteString)
import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy.Char8  as LBC8
import           Data.Swagger                (Schema, ToSchema)
import           GHC.Generics                (Generic)
import           Playground.API              (FunctionSchema)
import           Playground.Interpreter.Util
import           Playground.TH               (mkFunction, mkFunctions, mkSingleFunction)
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

printSchemas :: [FunctionSchema Schema] -> IO ()
printSchemas schemas =
    LBC8.putStrLn . encode $ schemas <> [payToPublicKey_Schema]

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . encode
