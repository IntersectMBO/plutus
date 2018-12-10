-- | Re-export functions that are needed when creating a Contract for use in the playground
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Playground.Contract
    ( mkFunction
    , ToSchema
    , Schema
    , ToJSON
    , FromJSON
    , FunctionSchema
    , Generic
    , payToPublicKey_
    , MockWallet
    , ByteString
    ) where

import           Data.Aeson            (FromJSON, ToJSON)
import           Data.ByteArray        (ByteArrayAccess)
import qualified Data.ByteArray        as BA
import           Data.ByteString.Lazy  (ByteString)
import qualified Data.ByteString.Lazy  as BSL
import           Data.Swagger          (Schema, ToSchema)
import           GHC.Generics          (Generic)
import           Playground.API        (FunctionSchema)
import           Playground.TH         (mkFunction)
import           Wallet.API            (payToPublicKey_)
import           Wallet.Emulator.Types (MockWallet)


-- We need to work with lazy 'ByteString's in contracts,
-- but 'ByteArrayAccess' (which we need for hashing) is only defined for strict
-- ByteStrings. With this orphan instance we can use lazy ByteStrings
-- throughout.

instance ByteArrayAccess ByteString where
    length = BA.length . BSL.toStrict
    withByteArray ba = BA.withByteArray (BSL.toStrict ba)
