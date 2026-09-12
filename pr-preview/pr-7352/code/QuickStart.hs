-- BLOCK1
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NumericUnderscores  #-}
{-# LANGUAGE OverloadedStrings   #-}

module Main where

import AuctionValidator
import Data.ByteString qualified as B
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Short qualified as BS
import PlutusLedgerApi.V1.Crypto qualified as Crypto
import PlutusLedgerApi.V1.Time qualified as Time
import PlutusLedgerApi.V1.Value qualified as Value
import PlutusLedgerApi.V3 (serialiseCompiledCode)
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteStringHex)

main :: IO ()
main =
  B.writeFile "validator.uplc.hex"
    $ Base16.encode
    $ BS.fromShort
    $ serialiseCompiledCode
    $ auctionValidatorScript AuctionParams
      { apSeller =
          -- Replace with the hex-encoded seller's public key hash:
          Crypto.PubKeyHash (
            stringToBuiltinByteStringHex
              "0000000000000000000000000000000000000000\
              \0000000000000000000000000000000000000000"
            )
      , apCurrencySymbol =
          -- Replace with your desired currency symbol (minting policy hash):
          Value.CurrencySymbol (
            stringToBuiltinByteStringHex
              "00000000000000000000000000000000000000000000000000000000"
            )
      , apTokenName =
          -- Replace with your desired token name:
          Value.tokenName "MY_TOKEN"
      , apMinBid =
          -- Minimal bid in lovelace:
          100
      , apEndTime =
          -- Replace with your desired end time in milliseconds:
          Time.fromMilliSeconds 1_725_227_091_000
      }
-- BLOCK2
