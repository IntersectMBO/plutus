{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# OPTIONS_GHC -Wno-orphans            #-}

module Plutus.V1.Ledger.Bytes ( LedgerBytes (..)
                , fromHex
                , bytes
                , fromBytes
                , encodeByteString
                ) where

import Control.DeepSeq (NFData)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Internal (c2w, w2c)
import Data.Either.Extras (unsafeFromEither)
import Data.String (IsString (..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TE
import Data.Word (Word8)
import GHC.Generics (Generic)
import PlutusTx qualified as PlutusTx
import PlutusTx.Lift
import PlutusTx.Prelude qualified as P
import Prettyprinter.Extras (Pretty, PrettyShow (..))

fromHex :: BS.ByteString -> Either String LedgerBytes
fromHex = fmap (LedgerBytes . P.toBuiltin) . asBSLiteral
    where

    handleChar :: Word8 -> Either String Word8
    handleChar x
        | x >= c2w '0' && x <= c2w '9' = Right (x - c2w '0') -- hexits 0-9
        | x >= c2w 'a' && x <= c2w 'f' = Right (x - c2w 'a' + 10) -- hexits a-f
        | x >= c2w 'A' && x <= c2w 'F' = Right (x - c2w 'A' + 10) -- hexits A-F
        | otherwise = Left ("not a hexit: " <> show (w2c x) <> "")

    -- turns a pair of bytes such as "a6" into a single Word8
    handlePair :: Word8 -> Word8 -> Either String Word8
    handlePair c c' = do
      n <- handleChar c
      n' <- handleChar c'
      pure $ (16 * n) + n'

    asBytes :: [Word8] -> Either String [Word8]
    asBytes []        = Right mempty
    asBytes (c:c':cs) = (:) <$> handlePair c c' <*> asBytes cs
    asBytes _         = Left "unpaired digit"

    -- parses a bytestring such as @a6b4@ into an actual bytestring
    asBSLiteral :: BS.ByteString -> Either String BS.ByteString
    asBSLiteral = withBytes asBytes
        where
          withBytes :: ([Word8] -> Either String [Word8]) -> BS.ByteString -> Either String BS.ByteString
          withBytes f = fmap BS.pack . f . BS.unpack

newtype LedgerBytes = LedgerBytes { getLedgerBytes :: P.BuiltinByteString }
    deriving stock (Eq, Ord, Generic)
    deriving newtype (P.Eq, P.Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    deriving anyclass (NFData)
    deriving Pretty via (PrettyShow LedgerBytes)

bytes :: LedgerBytes -> BS.ByteString
bytes = P.fromBuiltin . getLedgerBytes

fromBytes :: BS.ByteString -> LedgerBytes
fromBytes = LedgerBytes . P.toBuiltin

instance IsString LedgerBytes where
    fromString = unsafeFromEither . fromHex . fromString

instance Show LedgerBytes where
    show = Text.unpack . encodeByteString . bytes

encodeByteString :: BS.ByteString -> Text.Text
encodeByteString = TE.decodeUtf8 . Base16.encode

makeLift ''LedgerBytes
