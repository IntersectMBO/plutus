{-# LANGUAGE LambdaCase #-}

module PlutusLedgerApi.Common.Hash where

import PlutusCore.Crypto.Hash (blake2b_224)
import PlutusLedgerApi.Common.SerialisedScript
import PlutusLedgerApi.Common.Versions

import Data.ByteString qualified as B
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Short qualified as Short
import Data.Word

hashScript :: PlutusLedgerLanguage -> SerialisedScript -> B.ByteString
hashScript ll = hashScriptB ll . Short.fromShort
{-# INLINEABLE hashScript #-}

hashScriptHex :: PlutusLedgerLanguage -> B.ByteString -> Either String B.ByteString
hashScriptHex ll prg = hashScriptB ll <$> Base16.decode prg
{-# INLINEABLE hashScriptHex #-}

hashScriptB :: PlutusLedgerLanguage -> B.ByteString -> B.ByteString
hashScriptB ll prg =
  Base16.encode $ blake2b_224 (B.singleton (plutusVersionTag ll) <> prg)
{-# INLINEABLE hashScriptB #-}

plutusVersionTag :: PlutusLedgerLanguage -> Word8
plutusVersionTag = \case
  PlutusV1 -> 0x1
  PlutusV2 -> 0x2
  PlutusV3 -> 0x3
{-# INLINEABLE plutusVersionTag #-}
