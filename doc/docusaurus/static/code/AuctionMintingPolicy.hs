{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost        #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
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
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module AuctionMintingPolicy where

import PlutusTx
import PlutusTx.Prelude

import PlutusCore.Version (plcVersion110)
import PlutusLedgerApi.V1.Value (flattenValue)
import PlutusLedgerApi.V3 (PubKeyHash, ScriptContext (..), TxInfo (..), mintValueMinted)
import PlutusLedgerApi.V3.Contexts (ownCurrencySymbol, txSignedBy)

-- BLOCK1
type AuctionMintingParams = PubKeyHash
type AuctionMintingRedeemer = ()

auctionTypedMintingPolicy ::
  AuctionMintingParams ->
  AuctionMintingRedeemer ->
  ScriptContext ->
  Bool
auctionTypedMintingPolicy pkh _redeemer ctx =
  txSignedBy txInfo pkh && mintedExactlyOneToken
  where
    txInfo = scriptContextTxInfo ctx
    mintedExactlyOneToken =
      case flattenValue (mintValueMinted (txInfoMint txInfo)) of
        [(currencySymbol, _tokenName, quantity)] ->
          currencySymbol == ownCurrencySymbol ctx && quantity == 1
        _ -> False
-- BLOCK2
{-# INLINEABLE auctionTypedMintingPolicy #-}

auctionUntypedMintingPolicy ::
  AuctionMintingParams ->
  BuiltinData ->
  BuiltinData ->
  BuiltinUnit
auctionUntypedMintingPolicy pkh redeemer ctx =
  check
    ( auctionTypedMintingPolicy
        pkh
        (unsafeFromBuiltinData redeemer)
        (unsafeFromBuiltinData ctx)
    )

auctionMintingPolicyScript ::
  AuctionMintingParams ->
  CompiledCode (BuiltinData -> BuiltinData -> BuiltinUnit)
auctionMintingPolicyScript pkh =
  $$(compile [||auctionUntypedMintingPolicy||])
    `unsafeApplyCode` liftCode plcVersion110 pkh
