-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# LANGUAGE FlexibleContexts  #-}
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
    , SimpleArgumentSchema
    , ToJSON
    , FromJSON
    , FunctionSchema
    , Generic
    , payToWallet_
    , MockWallet
    , ByteString
    , printSchema
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
    , toSchema
    ) where

import qualified Control.Monad.Operational   as Op
import           Data.Aeson                  (FromJSON, ToJSON, encode)
import qualified Data.Aeson                  as Aeson
import           Data.ByteArray              (ByteArrayAccess)
import qualified Data.ByteArray              as BA
import           Data.ByteString.Lazy        (ByteString)
import qualified Data.ByteString.Lazy        as BSL
import qualified Data.ByteString.Lazy        as LBS
import qualified Data.ByteString.Lazy.Char8  as LBC8
import           Data.Either                 (fromRight)
import           Data.FileEmbed              (embedStringFile, makeRelativeToProject)
import           Data.List.NonEmpty          (NonEmpty ((:|)))
import           Data.Morpheus               ()
import           Data.Morpheus               (interpreter)
import           Data.Morpheus.Types         (GQLRequest (GQLRequest, operationName, query, variables))
import           Data.Morpheus.Types         ()
import           Data.Morpheus.Types         (GQLArgs, GQLResponse, GQLRootResolver (GQLRootResolver, mutationResolver, queryResolver, subscriptionResolver),
                                              MUTATION, ResolveCon, Resolver (Resolver), withEffect)
import           Data.Text                   (Text)
import qualified Data.Text                   as Text
import           Data.Text.Encoding          (decodeUtf8)
import           GHC.Generics                (Generic)
import           Ledger.Interval             (always)
import           Ledger.Tx                   (Tx)
import           Ledger.Validation           (ValidatorHash (ValidatorHash))
import           Ledger.Value                (TokenName (TokenName), Value)
import           Playground.API              (FunctionSchema, KnownCurrency (KnownCurrency), SchemaText (SchemaText),
                                              adaCurrency)
import           Playground.Interpreter.Util
import           Playground.TH               (mkFunction, mkFunctions, mkKnownCurrencies, mkSingleFunction)
import           Schema                      (SimpleArgumentSchema, ToSchema)
import           Wallet.API                  (MonadWallet, WalletAPI, WalletAPIError, payToPublicKey_)
import           Wallet.Emulator             (AssertionError, EmulatorState, addBlocksAndNotify,
                                              runTraceChainDefaultWallet, runWalletActionAndProcessPending,
                                              walletPubKey)
import           Wallet.Emulator.Types       (MockWallet, Wallet (..), runTraceChain)

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

printSchema :: (SchemaText, [KnownCurrency]) -> IO ()
printSchema (schema, currencies) =
    -- LBC8.putStrLn . encode $ (schemas <> [payToWallet_Schema], currencies) -- TODO Restore the addition of payToWallet
    LBC8.putStrLn . encode $ (schema, currencies)

printJson :: ToJSON a => a -> IO ()
printJson = LBC8.putStrLn . encode

introspectionQuery :: GQLRequest
introspectionQuery =
    GQLRequest
        { query =
              $(embedStringFile =<< makeRelativeToProject "data/introspection.gql")
        , operationName = Nothing
        , variables = Nothing
        }


toSchema :: (ResolveCon MockWallet q m s) => GQLRootResolver MockWallet q m s -> SchemaText
toSchema rootResolver = extractSchemaText $ runTraceChainDefaultWallet schemaM
  where
    extractSchemaText :: (Either AssertionError (Either WalletAPIError SchemaText, [Tx]), EmulatorState) -> SchemaText
    extractSchemaText (Right (Right t, _), _) = t
    extractSchemaText _                       = error "Fail"

    schemaResponse :: MockWallet GQLResponse
    schemaResponse = interpreter rootResolver introspectionQuery

    -- schemaM :: MonadWallet m => m SchemaText
    schemaM = SchemaText . decodeUtf8 . LBS.toStrict . Aeson.encode <$> schemaResponse
