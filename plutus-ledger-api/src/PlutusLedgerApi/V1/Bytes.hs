{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module PlutusLedgerApi.V1.Bytes
  ( LedgerBytes (..)
  , LedgerBytesError (..)
  , fromHex
  , bytes
  , fromBytes
  , encodeByteString
  ) where

import Control.DeepSeq (NFData)
import Control.Exception (Exception)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Internal (c2w, w2c)
import Data.Either.Extras (unsafeFromEither)
import Data.Function ((&))
import Data.String (IsString (..))
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TE
import Data.Word (Word8)
import GHC.Generics (Generic)
import PlutusTx (FromData, ToData, UnsafeFromData, makeLift)
import PlutusTx.Blueprint
  ( HasBlueprintDefinition
  , HasBlueprintSchema (..)
  , SchemaInfo (title)
  , withSchemaInfo
  )
import PlutusTx.Prelude qualified as P
import Prettyprinter.Extras (Pretty, PrettyShow (..))

-- | An error that is encountered when converting a `ByteString` to a `LedgerBytes`.
data LedgerBytesError
  = -- | Odd number of bytes in the original bytestring.
    UnpairedDigit
  | -- | A non-hex digit character ([^A-Fa-f0-9]) encountered during decoding.
    NotHexit !Char
  deriving stock (Show)
  deriving anyclass (Exception)

{-| Convert a hex-encoded (Base16) `ByteString` to a `LedgerBytes`.
     May return an error (`LedgerBytesError`). -}
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
    asBytes [] = Right mempty
    asBytes (c : c' : cs) = (:) <$> handlePair c c' <*> asBytes cs
    asBytes _ = Left UnpairedDigit

    -- parses a bytestring such as @a6b4@ into an actual bytestring
    asBSLiteral :: BS.ByteString -> Either LedgerBytesError BS.ByteString
    asBSLiteral = withBytes asBytes
      where
        withBytes
          :: ([Word8] -> Either LedgerBytesError [Word8])
          -> BS.ByteString
          -> Either LedgerBytesError BS.ByteString
        withBytes f = fmap BS.pack . f . BS.unpack

newtype LedgerBytes = LedgerBytes {getLedgerBytes :: P.BuiltinByteString}
  deriving stock (Eq, Ord, Generic)
  deriving newtype (P.Eq, P.Ord, PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
  deriving anyclass (NFData, HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow LedgerBytes)

instance HasBlueprintSchema LedgerBytes referencedTypes where
  {-# INLINEABLE schema #-}
  schema =
    schema @P.BuiltinByteString
      & withSchemaInfo \info -> info {title = Just "LedgerBytes"}

-- | Lift a Haskell bytestring to the Plutus abstraction 'LedgerBytes'
fromBytes :: BS.ByteString -> LedgerBytes
fromBytes = LedgerBytes . P.toBuiltin

-- | Extract the Haskell bytestring from inside the Plutus opaque 'LedgerBytes'.
bytes :: LedgerBytes -> BS.ByteString
bytes = P.fromBuiltin . getLedgerBytes

{-| Read in arbitrary 'LedgerBytes' as a \"string\" (of characters).

This is mostly used together with GHC's /OverloadedStrings/ extension
to specify at the source code any 'LedgerBytes' constants,
by utilizing Haskell's double-quoted string syntax.

IMPORTANT: the 'LedgerBytes' are expected to be already hex-encoded (base16); otherwise,
'LedgerBytesError' will be raised as an 'GHC.Exception.Exception'. -}
instance IsString LedgerBytes where
  fromString = unsafeFromEither . fromHex . fromString

{-| The `Show` instance of `LedgerBytes` is its Base16/Hex encoded bytestring,
decoded with UTF-8, unpacked to `String`. -}
instance Show LedgerBytes where
  show = Text.unpack . encodeByteString . bytes

{-| Encode a ByteString value to Base16 (i.e. hexadecimal), then
decode with UTF-8 to a `Text`. -}
encodeByteString :: BS.ByteString -> Text.Text
encodeByteString = TE.decodeUtf8 . Base16.encode

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''LedgerBytes)
