{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas -fno-omit-interface-pragmas #-}

module Example.Ual.Auction.OnChain (auction, outbids, params) where

import AuctionValidator
import PlutusLedgerApi.V3
import PlutusTx.Builtins.HasOpaque (stringToBuiltinByteStringHex)
import PlutusTx.Prelude

-- Same applied parameters as the upstream Auction/Properties.lean scenarios.
params :: AuctionParams
params =
  AuctionParams
    { apSeller =
        PubKeyHash
          ( stringToBuiltinByteStringHex
              "00000000000000000000000000000000000000000000000000000000000000000000000000000000"
          )
    , apCurrencySymbol =
        CurrencySymbol
          ( stringToBuiltinByteStringHex
              "00000000000000000000000000000000000000000000000000000000"
          )
    , apTokenName = tokenName "MY_TOKEN"
    , apMinBid = 100
    , apEndTime = 1725227091000
    }

{-# INLINEABLE auction #-}
auction :: BuiltinData -> BuiltinUnit
auction = auctionUntypedValidator params
