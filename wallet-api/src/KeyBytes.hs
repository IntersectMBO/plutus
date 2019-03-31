{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# OPTIONS_GHC -Wno-orphans            #-}

module KeyBytes ( KeyBytes (..)
                , fromHex
                , bytes
                , fromBytes
                ) where

import           Codec.Serialise
import           Data.Aeson                 (FromJSON (..), ToJSON (..))
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import           Data.Bifunctor             (bimap)
import qualified Data.ByteString.Lazy       as BSL
import           Data.String                (IsString (..))
import           Data.Swagger.Internal
import           Data.Swagger.Schema
import qualified Data.Text                  as Text
import           Data.Word                  (Word8)
import           GHC.Generics               (Generic)
import qualified Language.PlutusTx.Builtins as Builtins
import           Language.PlutusTx.Lift
import           Web.HttpApiData            (FromHttpApiData (..), ToHttpApiData (..))

fromHex :: BSL.ByteString -> KeyBytes
fromHex = KeyBytes . Builtins.SizedByteString . asBSLiteral
    where

    handleChar :: Word8 -> Word8
    handleChar x
        | x >= 48 && x <= 57 = x - 48 -- hexits 0-9
        | x >= 97 && x <= 102 = x - 87 -- hexits a-f
        | x >= 65 && x <= 70 = x - 55 -- hexits A-F
        | otherwise = error "not a hexit"

    -- turns a pair of bytes such as "a6" into a single Word8
    handlePair :: Word8 -> Word8 -> Word8
    handlePair c c' = 16 * handleChar c + handleChar c'

    asBytes :: [Word8] -> [Word8]
    asBytes []        = mempty
    asBytes (c:c':cs) = handlePair c c' : asBytes cs
    asBytes _         = error "unpaired digit"

    -- parses a bytestring such as @a6b4@ into an actual bytestring
    asBSLiteral :: BSL.ByteString -> BSL.ByteString
    asBSLiteral = withBytes asBytes
        where withBytes f = BSL.pack . f . BSL.unpack

newtype KeyBytes = KeyBytes { getKeyBytes :: Builtins.SizedByteString 32 } -- TODO: use strict bytestring
    deriving (Eq, Ord, IsString, Serialise, Generic)

bytes :: KeyBytes -> BSL.ByteString
bytes = Builtins.unSizedByteString . getKeyBytes

fromBytes :: BSL.ByteString -> KeyBytes
fromBytes = KeyBytes . Builtins.SizedByteString

instance Show KeyBytes where
    show = Text.unpack . JSON.encodeByteString . BSL.toStrict . bytes

instance ToSchema KeyBytes where
    declareNamedSchema _ = pure $ NamedSchema (Just "KeyBytes") byteSchema

instance ToJSON KeyBytes where
    toJSON = JSON.String . JSON.encodeByteString . BSL.toStrict . bytes

instance FromJSON KeyBytes where
    parseJSON v = fromBytes . BSL.fromStrict <$> JSON.decodeByteString v

instance ToHttpApiData KeyBytes where
    toUrlPiece = JSON.encodeByteString . BSL.toStrict . bytes

instance FromHttpApiData KeyBytes where
    parseUrlPiece = bimap Text.pack (fromBytes . BSL.fromStrict) . JSON.tryDecode

makeLift ''KeyBytes
