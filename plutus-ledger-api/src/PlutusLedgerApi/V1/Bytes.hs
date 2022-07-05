-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-orphans            #-}

module PlutusLedgerApi.V1.Bytes
    ( LedgerBytes (..)
    , fromHex
    , bytes
    , fromBytes
    , encodeByteString
    ) where

import Control.DeepSeq (NFData)
import Control.Exception
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Internal (c2w, w2c)
import Data.Either.Extras (unsafeFromEither)
import Data.String (IsString (..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TE
import Data.Word (Word8)
import GHC.Generics (Generic)
import PlutusTx
import PlutusTx.Prelude qualified as P
import Prettyprinter.Extras (Pretty, PrettyShow (..))

data LedgerBytesError =
    UnpairedDigit
    | NotHexit Char
    deriving stock (Show)
    deriving anyclass (Exception)

fromHex :: BS.ByteString -> Either LedgerBytesError LedgerBytes
fromHex = fmap (LedgerBytes . P.toBuiltin) . asBSLiteral
    where

    handleChar :: Word8 -> Either LedgerBytesError Word8
    handleChar x
        | x >= c2w '0' && x <= c2w '9' = Right (x - c2w '0') -- hexits 0-9
        | x >= c2w 'a' && x <= c2w 'f' = Right (x - c2w 'a' + 10) -- hexits a-f
        | x >= c2w 'A' && x <= c2w 'F' = Right (x - c2w 'A' + 10) -- hexits A-F
        | otherwise = Left $ NotHexit (w2c x)

    -- turns a pair of bytes such as "a6" into a single Word8
    handlePair :: Word8 -> Word8 -> Either LedgerBytesError Word8
    handlePair c c' = do
      n <- handleChar c
      n' <- handleChar c'
      pure $ (16 * n) + n'

    asBytes :: [Word8] -> Either LedgerBytesError [Word8]
    asBytes []        = Right mempty
    asBytes (c:c':cs) = (:) <$> handlePair c c' <*> asBytes cs
    asBytes _         = Left UnpairedDigit

    -- parses a bytestring such as @a6b4@ into an actual bytestring
    asBSLiteral :: BS.ByteString -> Either LedgerBytesError BS.ByteString
    asBSLiteral = withBytes asBytes
        where
          withBytes :: ([Word8] -> Either LedgerBytesError [Word8]) -> BS.ByteString -> Either LedgerBytesError BS.ByteString
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
