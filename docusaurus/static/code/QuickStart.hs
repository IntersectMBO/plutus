-- BLOCK1
{-# LANGUAGE ImportQualifiedPost #-}

module Main where

import AuctionValidator
import Data.ByteString qualified as B
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Short qualified as B
import PlutusLedgerApi.V2 qualified as V2

main :: IO ()
main = B.writeFile "validator.uplc" . Base16.encode $ B.fromShort serialisedScript
  where
    script = auctionValidatorScript params
    serialisedScript = V2.serialiseCompiledCode script
    params =
      AuctionParams
        { apSeller = error "Replace with seller's wallet address"
        , -- The asset to be auctioned is 10000 lovelaces
          apAsset = V2.singleton V2.adaSymbol V2.adaToken 10000
        , -- The minimum bid is 100 lovelaces
          apMinBid = 100
        , apEndTime = error "Replace with your desired end time"
        }
-- BLOCK2
