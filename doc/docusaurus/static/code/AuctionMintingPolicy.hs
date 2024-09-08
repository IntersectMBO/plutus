{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE Strict                     #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -fno-full-laziness #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-unbox-small-strict-fields #-}
{-# OPTIONS_GHC -fno-unbox-strict-fields #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.0.0 #-}

module AuctionMintingPolicy where

import PlutusLedgerApi.V1.Value (flattenValue)
import PlutusLedgerApi.V2 (PubKeyHash, ScriptContext (..), TxInfo (..))
import PlutusLedgerApi.V2.Contexts (ownCurrencySymbol, txSignedBy)
import PlutusTx.Prelude qualified as PlutusTx

type AuctionMintingParams = PubKeyHash
type AuctionMintingRedeemer = ()

auctionTypedMintingPolicy ::
  AuctionMintingParams ->
  AuctionMintingRedeemer ->
  ScriptContext ->
  Bool
auctionTypedMintingPolicy pkh _ ctx =
  txSignedBy txInfo pkh
    PlutusTx.&& mintedExactlyOneToken
  where
    txInfo = scriptContextTxInfo ctx
    mintedExactlyOneToken = case flattenValue (txInfoMint txInfo) of
      [(currencySymbol, _tokenName, 1)] -> currencySymbol == ownCurrencySymbol ctx
      _                                 -> False
