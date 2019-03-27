{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
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
import qualified Data.ByteString.Lazy       as BSL
import           Data.String                (IsString (..))
import           Data.Swagger.Internal
import           Data.Swagger.Schema
import qualified Data.Text                  as Text
import           Data.Word                  (Word8)
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
    deriving (Eq, Ord, IsString, Serialise)

bytes :: KeyBytes -> BSL.ByteString
bytes = Builtins.unSizedByteString . getKeyBytes

fromBytes :: BSL.ByteString -> KeyBytes
fromBytes = KeyBytes . Builtins.SizedByteString

instance Show KeyBytes where
    show = Text.unpack . JSON.encodeSerialise . bytes

-- drop the first 32 bytes of a private-public key pair
-- TODO: verify that this doesn't have sidechannels; maybe use ScrubbedBytes ??
-- dropPrivKey :: KeyBytes -> KeyBytes
-- dropPrivKey = KeyBytes . Builtins.SizedByteString . BSL.take 32 . BSL.drop 32 . Builtins.unSizedByteString . getKeyBytes

-- take the first 32 bytes of a private-public key pair
-- takePrivKey (KeyBytes bs) = KeyBytes (BSL.take 32 bs)

makeLift ''KeyBytes

instance ToSchema KeyBytes where
    declareNamedSchema _ = pure $ NamedSchema (Just "KeyBytes") byteSchema

instance ToJSON KeyBytes where
    toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON KeyBytes where
    parseJSON = JSON.decodeSerialise

instance ToHttpApiData KeyBytes where
    toUrlPiece = undefined

instance FromHttpApiData KeyBytes where
    parseUrlPiece = undefined
